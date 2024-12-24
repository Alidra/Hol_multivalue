Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := forall y0 : int, (int_lcm (@pair int int x0 y0)) = (@COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0)))).
Definition term12 := fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0.
Definition term55 (x0 : int) := forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int x0 y0)).
Definition term42 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> int_le (int_of_num (NUMERAL 0)) (div x0 x1).
Definition term28 (x0 : int) (x1 : int) := and (((int_mul x0 x1) = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term44 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (div x0 x1).
Definition term30 (x0 : int) (x1 : int) := @eq Prop ((fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (@COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))))).
Definition term15 := int_of_num (NUMERAL 0).
Definition term39 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_of_num (NUMERAL 0)) (div y0 y1)) x0.
Definition term34 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int y0 y1))) /\ ((int_divides (int_gcd (@pair int int y0 y1)) y0) /\ ((int_divides (int_gcd (@pair int int y0 y1)) y1) /\ (exists y2 : int, exists y3 : int, (int_gcd (@pair int int y0 y1)) = (int_add (int_mul y0 y2) (int_mul y1 y3)))))) x0.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lcm (@pair int int y0 y1)) = (@COND int ((int_mul y0 y1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul y0 y1)) (int_gcd (@pair int int y0 y1))))) x0.
Definition term35 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int x0 y0))) /\ ((int_divides (int_gcd (@pair int int x0 y0)) x0) /\ ((int_divides (int_gcd (@pair int int x0 y0)) y0) /\ (exists y1 : int, exists y2 : int, (int_gcd (@pair int int x0 y0)) = (int_add (int_mul x0 y1) (int_mul y0 y2))))).
Definition term19 (x0 : int) (x1 : int) := imp (~ ((int_mul x0 x1) = (int_of_num (NUMERAL 0)))).
Definition term20 (x0 : int) (x1 : int) := (~ ((int_mul x0 x1) = (int_of_num (NUMERAL 0)))) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term18 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term37 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int x0 x1))) /\ ((int_divides (int_gcd (@pair int int x0 x1)) x0) /\ ((int_divides (int_gcd (@pair int int x0 x1)) x1) /\ (exists y0 : int, exists y1 : int, (int_gcd (@pair int int x0 x1)) = (int_add (int_mul x0 y0) (int_mul x1 y1))))).
Definition term40 (x0 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term26 (x0 : int) (x1 : int) := ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term45 (x0 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (int_abs y0)) x0.
Definition term54 (x0 : int) (x1 : int) := ~ ((int_mul x0 x1) = (int_of_num (NUMERAL 0))).
Definition term41 (x0 : int) (x1 : int) := (fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0)) x1.
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term38 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int x0 x1)).
Definition term48 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) (int_abs (int_mul x0 x1))) /\ (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int x0 x1)))) -> (int_le (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)))) = True.
Definition term13 (x0 : int) (x1 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (@COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)))).
Definition term43 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1).
Definition term9 (x0 : int) (x1 : Prop) (x2 : int -> Prop) (x3 : int) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term32 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term10 (x0 : Prop) (x1 : int) (x2 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (@COND int x0 x1 x2).
Definition term27 (x0 : int) (x1 : int) := and (((int_mul x0 x1) = (int_of_num (NUMERAL 0))) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (int_of_num (NUMERAL 0))).
Definition term51 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs (int_mul x0 x1)).
Definition term25 (x0 : int) (x1 : int) := ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (int_of_num (NUMERAL 0)).
Definition term52 (x0 : int) (x1 : int) := and (int_le (int_of_num (NUMERAL 0)) (int_abs (int_mul x0 x1))).
Definition term14 (x0 : int) (x1 : int) := (((int_mul x0 x1) = (int_of_num (NUMERAL 0))) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (int_of_num (NUMERAL 0))) /\ ((~ ((int_mul x0 x1) = (int_of_num (NUMERAL 0)))) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)))).
Definition term49 (x0 : int) (x1 : int) := int_abs (int_mul x0 x1).
Definition term22 := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) (int_of_num (NUMERAL 0)).
Definition term24 (x0 : int) (x1 : int) := imp ((int_mul x0 x1) = (int_of_num (NUMERAL 0))).
Definition term56 := forall y0 : int, forall y1 : int, int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int y0 y1)).
Definition term21 (x0 : int) (x1 : int) := (~ ((int_mul x0 x1) = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term11 (x0 : int) (x1 : Prop) (x2 : int) := (x1 -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x0) /\ ((~ x1) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) y0) x2).
Definition term36 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int x0 y0))) /\ ((int_divides (int_gcd (@pair int int x0 y0)) x0) /\ ((int_divides (int_gcd (@pair int int x0 y0)) y0) /\ (exists y1 : int, exists y2 : int, (int_gcd (@pair int int x0 y0)) = (int_add (int_mul x0 y1) (int_mul y0 y2)))))) x1.
Definition term33 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term46 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term53 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (int_abs (int_mul x0 x1))) /\ (int_le (int_of_num (NUMERAL 0)) (int_gcd (@pair int int x0 x1))).
Definition term7 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (@COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)))).
Definition term3 (x0 : int) (x1 : int) := int_lcm (@pair int int x0 x1).
Definition term6 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int x0 x1)).
Definition term47 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> (int_le (int_of_num (NUMERAL 0)) (div x0 x1)) = True.
Definition term31 (x0 : int) (x1 : int) := @eq Prop (int_le (int_of_num (NUMERAL 0)) (@COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))))).
Definition term29 (x0 : int) (x1 : int) := (((int_mul x0 x1) = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ ((~ ((int_mul x0 x1) = (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)))).
Definition term50 (x0 : int) (x1 : int) := int_gcd (@pair int int x0 x1).
Definition term23 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term4 (x0 : int) (x1 : int) := @COND int ((int_mul x0 x1) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (int_lcm (@pair int int x0 y0)) = (@COND int ((int_mul x0 y0) = (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL 0)) (div (int_abs (int_mul x0 y0)) (int_gcd (@pair int int x0 y0))))) x1.
Definition term5 := int_le (int_of_num (NUMERAL 0)).
Definition term8 (x0 : int -> Prop) (x1 : Prop) (x2 : int) (x3 : int) := x0 (@COND int x1 x2 x3).
Definition term16 (x0 : int) (x1 : int) := div (int_abs (int_mul x0 x1)) (int_gcd (@pair int int x0 x1)).
