Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : real) := real_sub (real_abs x0) x0.
Definition term191 (x0 : real) := fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term325 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term135 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term300 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term180 (x0 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term110 (x0 : real) := (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term62 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real -> Prop) := ~ (all x0).
Definition term268 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term46 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term60 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)).
Definition term89 := fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))).
Definition term176 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term148 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term161 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term316 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term276 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term263 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term311 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term255 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term211 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term81 := fun y0 : real => (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term138 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term14 := real_of_num (NUMERAL 0).
Definition term33 (x0 : real) := real_neg (real_sub (real_abs x0) x0).
Definition term299 (x0 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term16 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0).
Definition term128 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term212 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term199 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term120 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term34 (x0 : real) := real_neg (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)).
Definition term213 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term250 (x0 : real) := (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))))) \/ (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term230 := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term291 (x0 : real) := (fun y0 : real => (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term205 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term146 (x0 : real) := real_gt (real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term273 := S (Nat.add (BIT1 0) 0).
Definition term5 := ~ (forall y0 : real, ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term57 (x0 : real) := real_gt (real_neg (real_sub (real_abs x0) x0)) (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term289 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0)).
Definition term313 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term258 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term105 := exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0))).
Definition term232 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term307 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term229 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term21 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term249 (x0 : real) := or (((real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term247 (x0 : real) := or (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))))).
Definition term36 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term156 (x0 : real) := real_gt (real_of_num (NUMERAL 0)) x0.
Definition term306 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term160 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term73 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term218 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term272 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term7 := fun y0 : real => ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term65 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term35 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)).
Definition term174 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term178 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term150 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term141 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term123 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term282 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term71 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term225 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term76 (x0 : real) := (~ ((real_abs x0) = x0)) /\ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term144 (x0 : real) := @eq real (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term187 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term226 (x0 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term308 := real_add (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term52 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term192 (x0 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term253 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term328 := ((~ (forall y0 : real, ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> False) -> forall y0 : real, ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term24 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term104 := exists y0 : real, (fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0.
Definition term99 := exists y0 : real, (fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0.
Definition term309 := real_mul (real_add (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term185 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term69 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term292 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term39 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term245 (x0 : real) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term294 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term43 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term55 (x0 : real) := real_gt (real_neg (real_sub (real_abs x0) x0)).
Definition term101 := or (exists y0 : real, (fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0).
Definition term67 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term12 := exists y0 : real, (((real_abs y0) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ ((real_abs y0) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term231 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term295 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term165 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term301 (x0 : real) := ((real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term183 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term122 (x0 : real) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term317 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term264 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term115 (x0 : real) := fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term224 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) x2.
Definition term243 (x0 : real) := and ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term281 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 := exists y0 : real, ~ ((fun y1 : real => ((real_abs y1) = y1) = (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term68 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term246 (x0 : real) := or ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term210 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term162 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term319 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term133 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term47 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term221 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term154 (x0 : real) := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term85 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term106 := (exists y0 : real, ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term270 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term70 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term18 (x0 : real) := @eq real (real_sub (real_abs x0) x0).
Definition term63 (x0 : real) := or (real_gt (real_sub (real_abs x0) x0) (real_of_num (NUMERAL 0))).
Definition term153 := and ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term139 := real_sub (real_of_num (NUMERAL 0)).
Definition term182 (x0 : real) := and ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))).
Definition term152 (x0 : real) := and ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) = (real_of_num (NUMERAL 0))).
Definition term145 := @eq real (real_of_num (NUMERAL 0)).
Definition term190 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) (real_neg x0))).
Definition term114 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0)) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_neg x0))).
Definition term284 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term86 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term208 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term169 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term312 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term257 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term51 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term186 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term127 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term61 (x0 : real) := real_gt (real_sub (real_abs x0) x0) (real_of_num (NUMERAL 0)).
Definition term240 (x0 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term130 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term11 := fun y0 : real => (((real_abs y0) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ ((real_abs y0) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term77 (x0 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term298 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term49 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term131 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term256 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term97 := @eq Prop (exists y0 : real, (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0))))).
Definition term96 := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0)).
Definition term75 (x0 : real) := and ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)))).
Definition term318 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term287 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term265 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term198 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) x0).
Definition term124 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0).
Definition term4 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term90 := fun y0 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0))).
Definition term170 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term251 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term283 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term32 (x0 : real) := (real_gt (real_sub (real_abs x0) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_abs x0) x0)) (real_of_num (NUMERAL 0))).
Definition term285 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term254 := S (Nat.add 0 0).
Definition term171 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term323 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term228 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term132 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term223 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term222 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term201 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term27 (x0 : real) := and ((real_abs x0) = x0).
Definition term116 (x0 : real) := (fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term29 (x0 : real) := ((real_abs x0) = x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term2 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term37 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term64 (x0 : real) := or (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))).
Definition term327 := (~ (forall y0 : real, ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> False.
Definition term271 := real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term168 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term1 (x0 : real) := (((real_abs x0) = x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0))) \/ ((~ ((real_abs x0) = x0)) /\ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term215 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term80 (x0 : real) := (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term158 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0)).
Definition term194 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) (real_neg x0)).
Definition term119 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_neg x0)).
Definition term219 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term209 (x0 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term184 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term279 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_neg (real_of_num x1)).
Definition term8 (x0 : real) := (fun y0 : real => ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0)) x0.
Definition term117 (x0 : real) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term136 := real_mul (real_of_num (NUMERAL 0)).
Definition term181 (x0 : real) := and ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) = (real_of_num (NUMERAL 0))).
Definition term28 (x0 : real) := and ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) = (real_of_num (NUMERAL 0))).
Definition term79 (x0 : real) := or (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term129 (x0 : real) := @eq Prop (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term234 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term216 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term25 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term172 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term17 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term166 := NUMERAL (BIT0 (BIT1 0)).
Definition term22 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term321 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term304 (x0 : real) := real_gt (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0).
Definition term277 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term50 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term95 := fun y0 : real => ((fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0).
Definition term244 (x0 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term193 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term189 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term87 := exists y0 : real, ((fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0).
Definition term163 := Nat.add (BIT1 0) (BIT1 0).
Definition term78 (x0 : real) := or (((real_abs x0) = x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term280 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term238 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term233 (x0 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)).
Definition term23 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term94 (x0 : real) := ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0) \/ ((fun y0 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))) x0).
Definition term202 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term41 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term324 := real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term259 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term173 (x0 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)).
Definition term329 := forall y0 : real, ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term93 (x0 : real) := (fun y0 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))) x0.
Definition term44 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term48 := real_of_num (NUMERAL (BIT1 0)).
Definition term177 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term149 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term121 (x0 : real) := (fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0.
Definition term91 (x0 : real) := (fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0.
Definition term164 := BIT0 (BIT1 0).
Definition term195 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) x0) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term239 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term235 (x0 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0)) (real_of_num (NUMERAL 0)).
Definition term103 := fun y0 : real => (fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0.
Definition term98 := fun y0 : real => (fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0.
Definition term56 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))).
Definition term179 (x0 : real) := @eq real (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))).
Definition term200 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) x0)).
Definition term126 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x0)).
Definition term100 := exists y0 : real, ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))).
Definition term137 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term19 (x0 : real) := @eq real (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)).
Definition term286 := real_mul (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term293 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term278 (x0 : real) := real_mul (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term40 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term269 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term204 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term196 (x0 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) x0.
Definition term9 (x0 : real) := ~ ((fun y0 : real => ((real_abs y0) = y0) = (real_le (real_of_num (NUMERAL 0)) y0)) x0).
Definition term297 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term290 (x0 : real) := forall y0 : real, (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0)).
Definition term10 := fun y0 : real => ~ ((fun y1 : real => ((real_abs y1) = y1) = (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term157 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0).
Definition term112 := exists y0 : real, (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0))))).
Definition term82 := exists y0 : real, (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term214 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term322 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term305 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term159 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term167 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term118 (x0 : real) := and (real_gt (real_of_num (NUMERAL 0)) x0).
Definition term188 (x0 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term42 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term92 (x0 : real) := or ((fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0).
Definition term109 (x0 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term175 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term147 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term143 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := real_gt (real_sub (real_abs x0) x0).
Definition term15 (x0 : real) := real_add (real_abs x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term288 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term266 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term220 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term197 (x0 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term58 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0)).
Definition term31 (x0 : real) := ~ ((real_abs x0) = x0).
Definition term113 (x0 : real) := (fun y0 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) (real_abs x0).
Definition term236 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term217 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term26 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term111 := fun y0 : real => (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0))))).
Definition term326 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term310 (x0 : real) := real_gt (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term134 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term155 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term125 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term314 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term274 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term260 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term241 (x0 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term142 := real_add (real_of_num (NUMERAL 0)).
Definition term102 := or (exists y0 : real, ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))).
Definition term72 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term66 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term248 (x0 : real) := (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))))) \/ (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term206 (x0 : real) := real_gt (real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term151 (x0 : real) := real_gt (real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term320 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term315 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term303 (x0 : real) := (((real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term275 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term262 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) := ~ (((real_abs x0) = x0) = (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term296 := Nat.mul (BIT1 0) (BIT0 (BIT1 0)).
Definition term54 (x0 : real) := @eq real (real_neg (real_sub (real_abs x0) x0)).
Definition term45 := NUMERAL (BIT1 0).
Definition term88 := (exists y0 : real, (fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0).
Definition term140 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term302 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term267 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term261 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term237 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term227 (x0 : real) := real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term252 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term203 (x0 : real) := @eq Prop ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_abs x0)) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term242 (x0 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0))) (real_of_num (NUMERAL 0))).
Definition term74 (x0 : real) := and (~ ((real_abs x0) = x0)).
Definition term207 := real_gt (real_of_num (NUMERAL 0)).
Definition term108 := @eq Prop ((exists y0 : real, ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_abs y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0))) (real_of_num (NUMERAL 0)))) /\ (real_ge y0 (real_of_num (NUMERAL 0))))).
Definition term107 := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_abs y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y1))) (real_of_num (NUMERAL 0)))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0)).
