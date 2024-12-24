Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term94 := fun y0 : int => forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term81 := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term19 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1))).
Definition term58 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term57 (x0 : int -> Prop) := ~ (all x0).
Definition term146 := (~ False) -> False.
Definition term18 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term37 (x0 : int) := or (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term100 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 (int_abs x1))) \/ (~ (@eq2 int y0 x0 (int_mod x1))))) x2.
Definition term29 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1))).
Definition term130 (x0 : Prop) := ~ (~ x0).
Definition term70 := fun y0 : int => exists y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ ((~ (int_lt y2 (int_abs y1))) \/ (~ (@eq2 int y2 y0 (int_mod y1))))).
Definition term32 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))).
Definition term27 (x0 : int) (x1 : int) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1))).
Definition term73 := int_of_num (NUMERAL 0).
Definition term20 (x0 : int) (x1 : int) := @eq2 int (rem x0 x1) x0 (int_mod x1).
Definition term50 (x0 : int) (x1 : int) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 (int_abs x1))) \/ (~ (@eq2 int y0 x0 (int_mod x1)))).
Definition term98 (x0 : int) := (fun y0 : int => forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1))))) x0.
Definition term96 (x0 : int) := (fun y0 : int => forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) x0.
Definition term67 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1)))) x0.
Definition term93 (x0 : int) := forall y0 : int, ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term109 (x0 : int) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term105 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term33 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_lt x0 (int_abs x2)) /\ (@eq2 int x0 x1 (int_mod x2))).
Definition term144 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> x0 = (int_of_num (NUMERAL 0)).
Definition term108 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term55 (x0 : int) (x1 : int) := ~ ((~ (x1 = (int_of_num (NUMERAL 0)))) -> exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1)))).
Definition term63 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 x0 (int_mod y1)))) y0).
Definition term49 (x0 : int) (x1 : int) := fun y0 : int => ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs x1)) /\ (@eq2 int y1 x0 (int_mod x1)))) y0).
Definition term45 (x0 : int) (x1 : int) := ~ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1)))).
Definition term77 (x0 : int) (x1 : int) := (~ (~ (x1 = (int_of_num (NUMERAL 0))))) \/ ((x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term141 (x0 : int) (x1 : int) := ~ (int_lt (rem x0 x1) (int_abs x1)).
Definition term145 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> False.
Definition term88 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term107 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term39 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((~ (int_lt x0 (int_abs x2))) \/ (~ (@eq2 int x0 x1 (int_mod x2)))).
Definition term136 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (@eq2 int x0 x1 (int_mod x2))))).
Definition term22 (x0 : int) := forall y0 : int, @eq2 int (rem x0 y0) x0 (int_mod y0).
Definition term97 (x0 : int) (x1 : int) := (fun y0 : int => @eq2 int (rem x0 y0) x0 (int_mod y0)) x1.
Definition term114 (x0 : int) (x1 : int) (x2 : int) := (~ (@eq2 int x1 x0 (int_mod x2))) \/ (~ (int_lt x1 (int_abs x2))).
Definition term111 (x0 : Prop) := (~ x0) -> x0.
Definition term53 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ (~ (exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1))))).
Definition term51 (x0 : int) (x1 : int) := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 (int_abs x1))) \/ (~ (@eq2 int y0 x0 (int_mod x1)))).
Definition term5 := ((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term23 := fun y0 : int => forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1).
Definition term127 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term31 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs y0)) /\ (@eq2 int y1 x0 (int_mod y0))).
Definition term68 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1)))) x0).
Definition term129 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))) /\ (~ (~ (@eq2 int x0 x1 (int_mod x2)))).
Definition term120 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term137 (x0 : int) (x1 : int) (x2 : int) := imp ((int_le (int_of_num (NUMERAL 0)) x0) /\ (@eq2 int x0 x1 (int_mod x2))).
Definition term35 (x0 : int) (x1 : int) := int_lt x0 (int_abs x1).
Definition term12 := (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term99 (x0 : int) (x1 : int) := (fun y0 : int => ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0))))) x1.
Definition term87 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1))).
Definition term131 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term118 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term16 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term47 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1)))) x2.
Definition term119 (x0 : int) (x1 : int) (x2 : int) := (~ (@eq2 int x1 x0 (int_mod x2))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_lt x1 (int_abs x2)))).
Definition term42 (x0 : int) (x1 : int) (x2 : int) := (int_lt x0 (int_abs x2)) /\ (@eq2 int x0 x1 (int_mod x2)).
Definition term44 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term65 (x0 : int) := exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ ((~ (int_lt y1 (int_abs y0))) \/ (~ (@eq2 int y1 x0 (int_mod y0))))).
Definition term122 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (@eq2 int x1 x0 (int_mod x2))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_lt x1 (int_abs x2))))).
Definition term123 (x0 : int) (x1 : int) (x2 : int) := (~ (int_lt x0 (int_abs x2))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (@eq2 int x0 x1 (int_mod x2)))).
Definition term8 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term74 (x0 : int) (x1 : int) := (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term64 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ ((~ (int_lt y1 (int_abs y0))) \/ (~ (@eq2 int y1 x0 (int_mod y0))))).
Definition term134 (x0 : int) (x1 : int) (x2 : int) := ~ (~ (@eq2 int x0 x1 (int_mod x2))).
Definition term61 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs y0)) /\ (@eq2 int y1 x0 (int_mod y0)))) x1.
Definition term117 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ (@eq2 int x1 x0 (int_mod x2))) \/ (~ (int_lt x1 (int_abs x2)))).
Definition term54 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ ((~ (int_lt y0 (int_abs x1))) \/ (~ (@eq2 int y0 x0 (int_mod x1))))).
Definition term126 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term102 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1)).
Definition term43 (x0 : int -> Prop) := ~ (ex x0).
Definition term59 (x0 : int) := ~ (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs y0)) /\ (@eq2 int y1 x0 (int_mod y0)))).
Definition term6 := (((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term113 (x0 : int) (x1 : int) := ~ (@eq2 int (rem x0 x1) x0 (int_mod x1)).
Definition term95 := forall y0 : int, forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term82 := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term24 := forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1).
Definition term10 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1))).
Definition term1 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))).
Definition term139 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (@eq2 int (rem x0 x1) x0 (int_mod x1)).
Definition term121 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((~ (int_lt x0 (int_abs x2))) \/ (~ (@eq2 int x0 x1 (int_mod x2))))).
Definition term78 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term110 (x0 : int) (x1 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term2 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> False.
Definition term80 (x0 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term36 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term103 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term25 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 (int_abs x2)) /\ (@eq2 int x0 x1 (int_mod x2))).
Definition term86 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term7 := (((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> ((~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term132 (x0 : int) := and (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term48 (x0 : int) (x1 : int) (x2 : int) := ~ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1)))) x2).
Definition term56 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term9 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term3 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1)))).
Definition term30 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs y0)) /\ (@eq2 int y1 x0 (int_mod y0))).
Definition term62 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs y0)) /\ (@eq2 int y1 x0 (int_mod y0)))) x1).
Definition term11 := imp (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)).
Definition term138 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ (@eq2 int x1 x0 (int_mod x2))) -> ~ (int_lt x1 (int_abs x2)).
Definition term101 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term90 (x0 : int) (x1 : int) := and ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))).
Definition term133 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term91 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))) /\ (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term28 (x0 : int) := imp (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term38 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ ((int_lt x0 (int_abs x2)) /\ (@eq2 int x0 x1 (int_mod x2)))).
Definition term21 (x0 : int) := fun y0 : int => @eq2 int (rem x0 y0) x0 (int_mod y0).
Definition term26 (x0 : int) (x1 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) /\ ((int_lt y0 (int_abs x1)) /\ (@eq2 int y0 x0 (int_mod x1))).
Definition term128 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (@eq2 int x0 x1 (int_mod x2)))).
Definition term124 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (@eq2 int x1 x0 (int_mod x2))))) -> ~ (int_lt x1 (int_abs x2)).
Definition term40 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_lt x0 (int_abs x2)) /\ (@eq2 int x0 x1 (int_mod x2)))).
Definition term92 (x0 : int) := fun y0 : int => ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term34 (x0 : int) (x1 : int) (x2 : int) := (~ (int_lt x0 (int_abs x2))) \/ (~ (@eq2 int x0 x1 (int_mod x2))).
Definition term72 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term13 := (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term135 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (@eq2 int x0 x1 (int_mod x2)).
Definition term125 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (@eq2 int x0 x1 (int_mod x2))).
Definition term17 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term85 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term84 (x0 : int) (x1 : int) := int_add (int_mul (div x0 x1) x1) (rem x0 x1).
Definition term66 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> exists y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) /\ ((int_lt y3 (int_abs y2)) /\ (@eq2 int y3 y1 (int_mod y2)))) y0).
Definition term60 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 x0 (int_mod y1)))) y0).
Definition term83 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term71 := exists y0 : int, exists y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (forall y2 : int, (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ ((~ (int_lt y2 (int_abs y1))) \/ (~ (@eq2 int y2 y0 (int_mod y1))))).
Definition term79 (x0 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term112 (x0 : int) (x1 : int) := (~ (@eq2 int (rem x0 x1) x0 (int_mod x1))) -> @eq2 int (rem x0 x1) x0 (int_mod x1).
Definition term41 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term89 (x0 : int) (x1 : int) := int_lt (rem x0 x1) (int_abs x1).
Definition term142 (x0 : int) (x1 : int) := (int_lt (rem x0 x1) (int_abs x1)) -> ~ (int_lt (rem x0 x1) (int_abs x1)).
Definition term76 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term75 (x0 : int) := or (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term4 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))) -> (forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term106 (x0 : int) (x1 : int) := @eq Prop ((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))).
Definition term115 (x0 : int) (x1 : int) (x2 : int) := ~ (@eq2 int x0 x1 (int_mod x2)).
Definition term52 (x0 : int) := and (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term14 := imp (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) /\ ((int_lt y2 (int_abs y1)) /\ (@eq2 int y2 y0 (int_mod y1))))).
Definition term104 (x0 : Prop) := x0 -> ~ x0.
Definition term140 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (@eq2 int (rem x0 x1) x0 (int_mod x1))) -> ~ (int_lt (rem x0 x1) (int_abs x1)).
Definition term69 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> exists y3 : int, (int_le (int_of_num (NUMERAL 0)) y3) /\ ((int_lt y3 (int_abs y2)) /\ (@eq2 int y3 y1 (int_mod y2)))) y0).
Definition term143 (x0 : int) (x1 : int) := (~ (int_lt (rem x0 x1) (int_abs x1))) -> x1 = (int_of_num (NUMERAL 0)).
Definition term116 (x0 : int) (x1 : int) := ~ (int_lt x0 (int_abs x1)).
Definition term46 (x0 : int) (x1 : int) := forall y0 : int, ~ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) /\ ((int_lt y1 (int_abs x1)) /\ (@eq2 int y1 x0 (int_mod x1)))) y0).
