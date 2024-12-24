Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow x1 x0) = (real_pow y0 x0))))) -> x1 = y0) x2.
Definition term39 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_abs x1)) /\ ((real_pow (real_abs x0) x2) = (real_pow (real_abs x1) x2)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ ((real_pow y1 y0) = (real_pow y2 y0))))) -> y1 = y2) x0.
Definition term32 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0)) x0.
Definition term33 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term24 := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ ((real_pow y1 y0) = (real_pow y2 y0))))) -> y1 = y2) -> forall y0 : real, forall y1 : real, (exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y0 y2) = (real_pow y1 y2))))) -> y0 = y1.
Definition term36 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term46 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow y0 x0) = (real_pow y1 x0))) -> (real_abs y0) = (real_abs y1).
Definition term23 := forall y0 : real, forall y1 : real, (exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y0 y2) = (real_pow y1 y2))))) -> y0 = y1.
Definition term12 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y0 x0) = (real_pow y1 x0))))) -> y0 = y1.
Definition term9 := forall y0 : real, forall y1 : nat, (real_pow (real_abs y0) y1) = (real_abs (real_pow y0 y1)).
Definition term8 := forall y0 : real, forall y1 : nat, (real_abs (real_pow y0 y1)) = (real_pow (real_abs y0) y1).
Definition term18 (x0 : real) (x1 : real) := (forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ ((real_pow y1 y0) = (real_pow y2 y0))))) -> y1 = y2) -> x0 = x1.
Definition term1 (x0 : real) (x1 : nat) := real_pow (real_abs x0) x1.
Definition term28 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term16 (x0 : nat) (x1 : real) (x2 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_le (real_of_num (NUMERAL 0)) x2) /\ ((real_pow x1 x0) = (real_pow x2 x0))))) -> x1 = x2.
Definition term43 (x0 : real) (x1 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x1)) /\ ((real_pow (real_abs x0) y0) = (real_pow (real_abs x1) y0)))).
Definition term30 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_abs y0) y1) = (real_abs (real_pow y0 y1))) x0.
Definition term31 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_abs x0) y0) = (real_abs (real_pow x0 y0))) x1.
Definition term22 (x0 : real) := forall y0 : real, (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow x0 y1) = (real_pow y0 y1))))) -> x0 = y0.
Definition term38 (x0 : real) (x1 : nat) := @eq real (real_abs (real_pow x0 x1)).
Definition term27 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term45 (x0 : nat) (x1 : real) := forall y0 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow y0 x0))) -> (real_abs x1) = (real_abs y0).
Definition term47 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_pow y1 y0) = (real_pow y2 y0))) -> (real_abs y1) = (real_abs y2).
Definition term10 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ ((real_pow y1 y0) = (real_pow y2 y0))))) -> y1 = y2.
Definition term7 := fun y0 : real => forall y1 : nat, (real_pow (real_abs y0) y1) = (real_abs (real_pow y0 y1)).
Definition term42 (x0 : real) (x1 : real) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x1)) /\ ((real_pow (real_abs x0) y0) = (real_pow (real_abs x1) y0)))).
Definition term19 (x0 : real) (x1 : real) := exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x0 y0) = (real_pow x1 y0)))).
Definition term41 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x1)) /\ ((real_pow (real_abs x0) x2) = (real_pow (real_abs x1) x2)))).
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : nat, (~ (y2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y0 y2) = (real_pow y1 y2))))) -> y0 = y1) x0.
Definition term3 (x0 : real) := fun y0 : nat => (real_pow (real_abs x0) y0) = (real_abs (real_pow x0 y0)).
Definition term2 (x0 : real) := fun y0 : nat => (real_abs (real_pow x0 y0)) = (real_pow (real_abs x0) y0).
Definition term29 (x0 : real) (x1 : real) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x1)) /\ ((real_pow (real_abs x0) y0) = (real_pow (real_abs x1) y0))))) -> (real_abs x0) = (real_abs x1).
Definition term13 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y0 x0) = (real_pow y1 x0))))) -> y0 = y1) x1.
Definition term35 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term6 := fun y0 : real => forall y1 : nat, (real_abs (real_pow y0 y1)) = (real_pow (real_abs y0) y1).
Definition term5 (x0 : real) := forall y0 : nat, (real_pow (real_abs x0) y0) = (real_abs (real_pow x0 y0)).
Definition term40 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_abs x1)) /\ ((real_pow (real_abs x0) x2) = (real_pow (real_abs x1) x2))).
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : nat, (~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow x0 y1) = (real_pow y0 y1))))) -> x0 = y0) x1.
Definition term20 (x0 : real) (x1 : real) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x0 y0) = (real_pow x1 y0)))).
Definition term17 (x0 : real) (x1 : real) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x0 x2) = (real_pow x1 x2)))).
Definition term14 (x0 : nat) (x1 : real) := forall y0 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow x1 x0) = (real_pow y0 x0))))) -> x1 = y0.
Definition term37 (x0 : real) (x1 : nat) := @eq real (real_pow (real_abs x0) x1).
Definition term34 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term0 (x0 : real) (x1 : nat) := real_abs (real_pow x0 x1).
Definition term4 (x0 : real) := forall y0 : nat, (real_abs (real_pow x0 y0)) = (real_pow (real_abs x0) y0).
Definition term21 (x0 : real) (x1 : real) := (exists y0 : nat, (~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x0 y0) = (real_pow x1 y0))))) -> x0 = x1.
Definition term44 (x0 : nat) (x1 : real) (x2 : real) := ((~ (x0 = (NUMERAL 0))) /\ ((real_pow x1 x0) = (real_pow x2 x0))) -> (real_abs x1) = (real_abs x2).
