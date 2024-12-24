Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term61 := fun y0 : int => forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term49 := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term20 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1).
Definition term16 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1))).
Definition term26 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term25 (x0 : int -> Prop) := ~ (all x0).
Definition term75 := (~ False) -> False.
Definition term4 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term15 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term18 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0).
Definition term41 := int_of_num (NUMERAL 0).
Definition term63 (x0 : int) := (fun y0 : int => forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1))))) x0.
Definition term35 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) x0.
Definition term60 (x0 : int) := forall y0 : int, ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term72 (x0 : int) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term32 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))).
Definition term69 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term17 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term31 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y1)) y0).
Definition term45 (x0 : int) (x1 : int) := (~ (~ (x1 = (int_of_num (NUMERAL 0))))) \/ ((x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term24 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term71 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term73 (x0 : Prop) := (~ x0) -> x0.
Definition term36 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) x0).
Definition term64 (x0 : int) (x1 : int) := (fun y0 : int => ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0))))) x1.
Definition term55 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1))).
Definition term13 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term8 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term21 (x0 : int) (x1 : int) := ~ ((~ (x1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term42 (x0 : int) (x1 : int) := (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term6 := (((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term27 (x0 : int) := ~ (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0)).
Definition term22 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))).
Definition term62 := forall y0 : int, forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term50 := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term10 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1))).
Definition term1 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1).
Definition term19 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0).
Definition term46 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term65 (x0 : int) (x1 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term2 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> False.
Definition term48 (x0 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term67 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term54 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term29 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) x1.
Definition term23 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term9 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term3 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1)).
Definition term30 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) x1).
Definition term66 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term57 (x0 : int) (x1 : int) := and ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))).
Definition term58 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))) /\ (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term33 (x0 : int) := exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))).
Definition term59 (x0 : int) := fun y0 : int => ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term74 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) -> False.
Definition term12 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term40 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term14 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term53 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term52 (x0 : int) (x1 : int) := int_add (int_mul (div x0 x1) x1) (rem x0 x1).
Definition term34 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)) y0).
Definition term28 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 y1)) y0).
Definition term51 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term39 := exists y0 : int, exists y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))).
Definition term47 (x0 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term56 (x0 : int) (x1 : int) := int_lt (rem x0 x1) (int_abs x1).
Definition term5 := ((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term44 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term7 := (((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> ((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term38 := fun y0 : int => exists y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))).
Definition term43 (x0 : int) := or (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term70 (x0 : int) (x1 : int) := @eq Prop ((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))).
Definition term11 := imp (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y0 y1))).
Definition term68 (x0 : Prop) := x0 -> ~ x0.
Definition term37 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem y1 y2)) y0).
