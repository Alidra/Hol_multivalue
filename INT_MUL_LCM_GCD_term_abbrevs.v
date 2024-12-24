Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term80 (x0 : int) (x1 : int) (x2 : int) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term46 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul (int_gcd (@pair int int x0 y0)) (int_lcm (@pair int int x0 y0))) = (int_abs (int_mul x0 y0))) x1.
Definition term33 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0))) x1.
Definition term30 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term29 (x0 : int -> Prop) := ~ (all x0).
Definition term85 := (~ False) -> False.
Definition term58 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term73 (x0 : Prop) := ~ (~ x0).
Definition term27 (x0 : int) := forall y0 : int, (int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0)).
Definition term22 (x0 : int) := forall y0 : int, (int_mul (int_gcd (@pair int int x0 y0)) (int_lcm (@pair int int x0 y0))) = (int_abs (int_mul x0 y0)).
Definition term72 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term47 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) x0.
Definition term45 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) x0.
Definition term40 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) x0.
Definition term76 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term78 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term77 (x0 : int) (x1 : int) (x2 : int) := (x1 = x0) /\ (x1 = x2).
Definition term36 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (int_mul (int_lcm (@pair int int x0 y1)) (int_gcd (@pair int int x0 y1))) = (int_abs (int_mul x0 y1))) y0).
Definition term38 (x0 : int) := exists y0 : int, ~ ((int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0))).
Definition term66 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term83 (x0 : int) (x1 : int) := (~ ((int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))) = (int_abs (int_mul x0 x1)))) -> (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))) = (int_abs (int_mul x0 x1)).
Definition term55 (x0 : int) (x1 : int) := (~ ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_abs (int_mul x0 x1)))) -> (int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_abs (int_mul x0 x1)).
Definition term54 (x0 : Prop) := (~ x0) -> x0.
Definition term5 := ((~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term84 (x0 : int) (x1 : int) := ((int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))) = (int_abs (int_mul x0 x1))) -> False.
Definition term68 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term70 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term41 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) x0).
Definition term64 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term37 (x0 : int) := fun y0 : int => ~ ((int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0))).
Definition term65 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term12 := (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term62 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> ~ (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)).
Definition term28 := fun y0 : int => forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)).
Definition term23 := fun y0 : int => forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)).
Definition term49 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term48 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul x0 y0) = (int_mul y0 x0)) x1.
Definition term8 := (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term25 (x0 : int) (x1 : int) := int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1)).
Definition term26 (x0 : int) := fun y0 : int => (int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0)).
Definition term17 (x0 : int) := forall y0 : int, (int_mul x0 y0) = (int_mul y0 x0).
Definition term69 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term20 (x0 : int) (x1 : int) := int_abs (int_mul x0 x1).
Definition term31 (x0 : int) := ~ (forall y0 : int, (int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0))).
Definition term63 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term6 := (((~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term67 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term19 (x0 : int) (x1 : int) := int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1)).
Definition term24 := forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)).
Definition term10 := forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0).
Definition term1 := forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)).
Definition term56 (x0 : int) (x1 : int) := ~ ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_abs (int_mul x0 x1))).
Definition term35 (x0 : int) (x1 : int) := ~ ((int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))) = (int_abs (int_mul x0 x1))).
Definition term2 := (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> False.
Definition term18 := fun y0 : int => forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0).
Definition term61 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 := (((~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> ((~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term75 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term9 := ~ (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)).
Definition term3 := ~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))).
Definition term59 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term34 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (int_mul (int_lcm (@pair int int x0 y0)) (int_gcd (@pair int int x0 y0))) = (int_abs (int_mul x0 y0))) x1).
Definition term11 := imp (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))).
Definition term53 (x0 : int) (x1 : int) := ~ ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1)))).
Definition term21 (x0 : int) := fun y0 : int => (int_mul (int_gcd (@pair int int x0 y0)) (int_lcm (@pair int int x0 y0))) = (int_abs (int_mul x0 y0)).
Definition term81 (x0 : int) (x1 : int) := ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1)))) /\ ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_abs (int_mul x0 x1))).
Definition term71 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term50 (x0 : int) (x1 : int) := int_lcm (@pair int int x0 x1).
Definition term13 := (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> ~ (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)).
Definition term43 := fun y0 : int => exists y1 : int, ~ ((int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))).
Definition term79 (x0 : int) (x1 : int) (x2 : int) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term39 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (int_mul (int_lcm (@pair int int y1 y2)) (int_gcd (@pair int int y1 y2))) = (int_abs (int_mul y1 y2))) y0).
Definition term32 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (int_mul (int_lcm (@pair int int x0 y1)) (int_gcd (@pair int int x0 y1))) = (int_abs (int_mul x0 y1))) y0).
Definition term44 := exists y0 : int, exists y1 : int, ~ ((int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))).
Definition term51 (x0 : int) (x1 : int) := int_gcd (@pair int int x0 x1).
Definition term57 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term16 (x0 : int) := fun y0 : int => (int_mul x0 y0) = (int_mul y0 x0).
Definition term74 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term60 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term52 (x0 : int) (x1 : int) := (~ ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))))) -> (int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))).
Definition term4 := (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))) -> (forall y0 : int, forall y1 : int, (int_mul (int_gcd (@pair int int y0 y1)) (int_lcm (@pair int int y0 y1))) = (int_abs (int_mul y0 y1))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term14 := imp (~ (forall y0 : int, forall y1 : int, (int_mul (int_lcm (@pair int int y0 y1)) (int_gcd (@pair int int y0 y1))) = (int_abs (int_mul y0 y1)))).
Definition term42 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (int_mul (int_lcm (@pair int int y1 y2)) (int_gcd (@pair int int y1 y2))) = (int_abs (int_mul y1 y2))) y0).
Definition term82 (x0 : int) (x1 : int) := (((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1)))) /\ ((int_mul (int_gcd (@pair int int x0 x1)) (int_lcm (@pair int int x0 x1))) = (int_abs (int_mul x0 x1)))) -> (int_mul (int_lcm (@pair int int x0 x1)) (int_gcd (@pair int int x0 x1))) = (int_abs (int_mul x0 x1)).
