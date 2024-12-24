Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (x0 : real) := @eq Prop ((real_neg (sqrt x0)) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term53 (x0 : real) := (fun y0 : real => (sqrt (real_neg y0)) = (real_neg (sqrt y0))) x0.
Definition term39 (x0 : real) := (fun y0 : Prop => (sqrt x0) = (sqrt (@COND real y0 x0 (real_neg x0)))) True.
Definition term56 (x0 : real) := @eq real (real_neg (sqrt x0)).
Definition term37 (x0 : real) := fun y0 : Prop => (sqrt x0) = (sqrt (@COND real y0 x0 (real_neg x0))).
Definition term29 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term44 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> (real_le (real_of_num (NUMERAL 0)) x0) = False.
Definition term31 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (sqrt x0) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term20 (x0 : real) (x1 : Prop) (x2 : real) (x3 : real) := (x1 -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x2) x2 (real_neg x2)))) x0) /\ ((~ x1) -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x2) x2 (real_neg x2)))) x3).
Definition term49 (x0 : real) := @eq Prop ((fun y0 : Prop => (real_neg (sqrt x0)) = (sqrt (@COND real y0 x0 (real_neg x0)))) (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term41 (x0 : real) := @eq Prop ((fun y0 : Prop => (sqrt x0) = (sqrt (@COND real y0 x0 (real_neg x0)))) (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term12 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) (sqrt x0) (real_neg (sqrt x0)).
Definition term8 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0).
Definition term10 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) (sqrt x0).
Definition term25 (x0 : real) := imp (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term45 (x0 : real) := fun y0 : Prop => (real_neg (sqrt x0)) = (sqrt (@COND real y0 x0 (real_neg x0))).
Definition term54 (x0 : real) := sqrt (real_neg x0).
Definition term43 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term27 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> (real_neg (sqrt x0)) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term5 (x0 : real) := real_abs (sqrt x0).
Definition term15 (x0 : real) := sqrt (real_abs x0).
Definition term18 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term30 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (sqrt x0).
Definition term48 (x0 : real) := sqrt (@COND real False x0 (real_neg x0)).
Definition term1 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term14 (x0 : real) := @eq real (@COND real (real_le (real_of_num (NUMERAL 0)) x0) (sqrt x0) (real_neg (sqrt x0))).
Definition term47 (x0 : real) := (fun y0 : Prop => (real_neg (sqrt x0)) = (sqrt (@COND real y0 x0 (real_neg x0)))) False.
Definition term6 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) (sqrt x0) (real_neg (sqrt x0)).
Definition term55 (x0 : real) := @COND real False x0 (real_neg x0).
Definition term7 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term21 (x0 : real) := fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0))).
Definition term33 (x0 : real) := and ((real_le (real_of_num (NUMERAL 0)) x0) -> (sqrt x0) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term16 (x0 : real) := sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)).
Definition term42 (x0 : real) := @eq Prop ((sqrt x0) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term2 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term3 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term28 (x0 : real) := (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (sqrt x0).
Definition term4 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term26 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (real_neg (sqrt x0)).
Definition term36 (x0 : real) := @eq Prop ((@COND real (real_le (real_of_num (NUMERAL 0)) x0) (sqrt x0) (real_neg (sqrt x0))) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term57 := forall y0 : real, (real_abs (sqrt y0)) = (sqrt (real_abs y0)).
Definition term11 (x0 : real) := real_neg (sqrt x0).
Definition term35 (x0 : real) := @eq Prop ((fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (@COND real (real_le (real_of_num (NUMERAL 0)) x0) (sqrt x0) (real_neg (sqrt x0)))).
Definition term17 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term23 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (sqrt x0)) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (real_neg (sqrt x0))).
Definition term9 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) (sqrt x0).
Definition term46 (x0 : real) := (fun y0 : Prop => (real_neg (sqrt x0)) = (sqrt (@COND real y0 x0 (real_neg x0)))) (real_le (real_of_num (NUMERAL 0)) x0).
Definition term38 (x0 : real) := (fun y0 : Prop => (sqrt x0) = (sqrt (@COND real y0 x0 (real_neg x0)))) (real_le (real_of_num (NUMERAL 0)) x0).
Definition term32 (x0 : real) := and ((real_le (real_of_num (NUMERAL 0)) x0) -> (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (sqrt x0)).
Definition term13 (x0 : real) := @eq real (real_abs (sqrt x0)).
Definition term52 (x0 : real) := @eq real (sqrt x0).
Definition term22 (x0 : real) := (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (@COND real (real_le (real_of_num (NUMERAL 0)) x0) (sqrt x0) (real_neg (sqrt x0))).
Definition term19 (x0 : real) (x1 : Prop) (x2 : real) (x3 : real) := (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (@COND real x1 x2 x3).
Definition term40 (x0 : real) := sqrt (@COND real True x0 (real_neg x0)).
Definition term34 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) -> (sqrt x0) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) /\ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) -> (real_neg (sqrt x0)) = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))).
Definition term0 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) = (real_le (real_of_num (NUMERAL 0)) y0)) x0.
Definition term24 (x0 : real) := (fun y0 : real => y0 = (sqrt (@COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0)))) (real_neg (sqrt x0)).
Definition term51 (x0 : real) := @COND real True x0 (real_neg x0).
