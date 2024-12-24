Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term54 (x0 : int) (x1 : int) := (x0 = x1) /\ (@eq2 int x0 x1 (int_mod (int_of_num (NUMERAL 0)))).
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term162 (x0 : int) (x1 : int) := int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term91 := fun y0 : int => forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)).
Definition term6 (x0 : int) := fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1)).
Definition term5 (x0 : int) := fun y0 : int => forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term18 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1))) x1.
Definition term97 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term96 (x0 : int -> Prop) := ~ (all x0).
Definition term51 := int_mod (int_of_num (NUMERAL 0)).
Definition term212 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term157 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x0 = x1) /\ (~ (y0 = y1))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y0)) = (int_add x1 (int_mul (int_of_num (NUMERAL (BIT1 0))) y1)))) x2.
Definition term149 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4)))) -> forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4))).
Definition term10 := fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2)).
Definition term9 := fun y0 : int => forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term112 (x0 : int) (x1 : int) := (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)))) /\ (~ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0)))).
Definition term255 (x0 : int) (x1 : int) (x2 : int) := (((rem x0 x1) = x2) -> (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) /\ (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2).
Definition term150 (x0 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4)))) x0.
Definition term22 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term179 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term79 (x0 : int) (x1 : int) := int_add (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0)).
Definition term74 (x0 : int) (x1 : int) := int_add (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term169 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term252 (x0 : int) (x1 : int) (x2 : int) := ((((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> ((rem x0 x2) = x1) = True) -> (((((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2))) -> (rem x0 x2) = x1) = ((((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> True).
Definition term219 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term115 (x0 : int) (x1 : int) := ~ ((int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) = (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))))).
Definition term73 (x0 : int) (x1 : int) := int_sub (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0)).
Definition term67 (x0 : int) (x1 : int) := (x1 = x0) -> x0 = x1.
Definition term139 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := forall y0 : int, (~ (x3 = (int_of_num (NUMERAL 0)))) -> ((x0 = x2) /\ (~ (x1 = y0))) -> ~ ((int_add x0 (int_mul x3 x1)) = (int_add x2 (int_mul x3 y0))).
Definition term21 := int_of_num (NUMERAL 0).
Definition term155 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((x0 = y0) /\ (~ (y1 = y2))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y1)) = (int_add y0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y2)))) x1.
Definition term134 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) -> ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul x0 y2)) = (int_add y1 (int_mul x0 y3)))) x1.
Definition term43 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term223 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) = True.
Definition term126 (x0 : int) (x1 : int) := int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))).
Definition term65 (x0 : int) (x1 : int) := imp ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))).
Definition term175 (x0 : int) (x1 : int) := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))).
Definition term248 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := ((((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> ((rem x0 x2) = x1) = x3) -> (((((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2))) -> (rem x0 x2) = x1) = ((((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> x3).
Definition term231 (x0 : int) := (fun y0 : int => forall y1 : int, ((rem y0 y1) = y0) = ((y1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs y1))))) x0.
Definition term211 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) x0.
Definition term106 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))) x0.
Definition term13 (x0 : int) := (fun y0 : int => forall y1 : int, (rem (rem y0 y1) y1) = (rem y0 y1)) x0.
Definition term50 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term141 (x0 : int) (x1 : int) (x2 : int) (x3 : int) (x4 : int) := (~ (x3 = (int_of_num (NUMERAL 0)))) -> ((x0 = x2) /\ (~ (x1 = x4))) -> ~ ((int_add x0 (int_mul x3 x1)) = (int_add x2 (int_mul x3 x4))).
Definition term183 (x0 : int) := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term123 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term16 (x0 : int) (x1 : int) := rem (rem x0 x1) x1.
Definition term27 (x0 : int) (x1 : int) := ~ ((int_le x1 x0) /\ (int_lt x0 x1)).
Definition term153 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y2)) = (int_add y1 (int_mul (int_of_num (NUMERAL (BIT1 0))) y3)))) x0.
Definition term132 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4)))) x0.
Definition term17 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2))) x0.
Definition term160 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x0 = x2) /\ (~ (x1 = x3))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) x1)) = (int_add x2 (int_mul (int_of_num (NUMERAL (BIT1 0))) x3))).
Definition term142 (x0 : int) (x1 : int) (x2 : int) (x3 : int) (x4 : int) := ((x0 = x2) /\ (~ (x1 = x4))) -> ~ ((int_add x0 (int_mul x3 x1)) = (int_add x2 (int_mul x3 x4))).
Definition term247 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := (((((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2))) = (((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2)))) -> ((((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> ((rem x0 x2) = x1) = x3) -> (((((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2))) -> (rem x0 x2) = x1) = ((((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> x3).
Definition term102 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y1) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))) y0).
Definition term121 (x0 : int) (x1 : int) := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term251 (x0 : int) (x1 : int) (x2 : int) := (((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1))) /\ ((rem x0 x1) = (rem x2 x1))) -> ((rem x0 x1) = x2) = True.
Definition term161 (x0 : int) (x1 : int) := (((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))) = (int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))))) /\ (~ ((int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) = (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))))))) -> ~ ((int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))))) = (int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))))))).
Definition term148 := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4))).
Definition term174 (x0 : int) (x1 : int) := int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term191 (x0 : int) (x1 : int) := @eq int (int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))))).
Definition term38 (x0 : int) (x1 : int) := True /\ (x0 = x1).
Definition term218 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term58 (x0 : int) (x1 : int) := ((x0 = x1) /\ (exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0))) -> x0 = x1.
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0))) x2.
Definition term189 (x0 : int) := int_add (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term176 (x0 : int) (x1 : int) := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term35 := @eq int (int_of_num (NUMERAL 0)).
Definition term234 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs x1))).
Definition term136 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (~ (x1 = (int_of_num (NUMERAL 0)))) -> ((x0 = y0) /\ (~ (y1 = y2))) -> ~ ((int_add x0 (int_mul x1 y1)) = (int_add y0 (int_mul x1 y2)))) x2.
Definition term100 (x0 : int) (x1 : int) := (fun y0 : int => ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0))) x1.
Definition term127 (x0 : int) (x1 : int) := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))) = (int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0))))) /\ (~ ((int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) = (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))))).
Definition term46 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_of_num (NUMERAL 0))).
Definition term192 := ~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))).
Definition term49 (x0 : int) (x1 : int) (x2 : int) := and (((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))).
Definition term69 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) x0.
Definition term26 (x0 : int) (x1 : int) := (fun y0 : int => ~ ((int_le x0 y0) /\ (int_lt y0 x0))) x1.
Definition term107 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))) x0).
Definition term2 (x0 : int) (x1 : int) := fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0)).
Definition term41 := int_abs (int_of_num (NUMERAL 0)).
Definition term42 (x0 : int) (x1 : int) := int_lt x0 (int_abs x1).
Definition term163 (x0 : int) (x1 : int) := int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term239 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) = y0) -> (y0 -> ((rem x0 x1) = x2) = y1) -> (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2) = (y0 -> y1)) x3.
Definition term47 (x0 : int) (x1 : int) (x2 : int) := ((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))).
Definition term172 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))))).
Definition term37 (x0 : int) (x1 : int) (x2 : int) := (x0 = (int_of_num (NUMERAL 0))) /\ (x1 = x2).
Definition term94 (x0 : int) (x1 : int) := ~ (((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))).
Definition term214 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term140 (x0 : int) (x1 : int) (x2 : int) (x3 : int) (x4 : int) := (fun y0 : int => (~ (x3 = (int_of_num (NUMERAL 0)))) -> ((x0 = x2) /\ (~ (x1 = y0))) -> ~ ((int_add x0 (int_mul x3 x1)) = (int_add x2 (int_mul x3 y0)))) x4.
Definition term88 (x0 : int) (x1 : int) := @eq int (int_sub (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))).
Definition term173 (x0 : int) (x1 : int) := int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0))).
Definition term178 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))).
Definition term81 (x0 : int) (x1 : int) := fun y0 : int => (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0).
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0)).
Definition term24 (x0 : int) := (fun y0 : int => forall y1 : int, ~ ((int_le y0 y1) /\ (int_lt y1 y0))) x0.
Definition term195 (x0 : int) (x1 : int) := ~ (((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))))).
Definition term1 (x0 : int) (x1 : int) := fun y0 : int => ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term226 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = (rem x0 x1))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term56 (x0 : int) (x1 : int) := exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0).
Definition term235 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term164 (x0 : int) (x1 : int) := ~ ((int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))))) = (int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))))))).
Definition term187 := int_add (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0))).
Definition term253 (x0 : int) (x1 : int) (x2 : int) := ((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2.
Definition term120 := int_mul (int_of_num (NUMERAL (BIT1 0))).
Definition term138 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => forall y1 : int, (~ (x2 = (int_of_num (NUMERAL 0)))) -> ((x0 = x1) /\ (~ (y0 = y1))) -> ~ ((int_add x0 (int_mul x2 y0)) = (int_add x1 (int_mul x2 y1)))) x3.
Definition term82 (x0 : int) (x1 : int) := fun y0 : int => (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)).
Definition term159 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((x0 = x2) /\ (~ (x1 = y0))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) x1)) = (int_add x2 (int_mul (int_of_num (NUMERAL (BIT1 0))) y0)))) x3.
Definition term225 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_lt (rem x0 x1) (int_abs x1)) = True.
Definition term45 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs x1)).
Definition term15 (x0 : int) (x1 : int) := (fun y0 : int => (rem (rem x0 y0) y0) = (rem x0 y0)) x1.
Definition term71 (x0 : int) (x1 : int) := int_sub (int_sub x0 x1).
Definition term198 := (exists y0 : int, exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))))) -> False.
Definition term185 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term215 (x0 : int) (x1 : int) := (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term83 (x0 : int) (x1 : int) := exists y0 : int, (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)).
Definition term256 (x0 : int) (x1 : int) := forall y0 : int, ((rem x0 x1) = y0) = ((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = y0)) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) /\ (@eq2 int x0 y0 (int_mod x1))).
Definition term232 (x0 : int) := forall y0 : int, ((rem x0 y0) = x0) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0)))).
Definition term168 := int_add (int_of_num (NUMERAL 0)).
Definition term39 (x0 : int) (x1 : int) (x2 : int) := or ((x0 = (int_of_num (NUMERAL 0))) /\ (x1 = x2)).
Definition term122 := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)).
Definition term199 (x0 : Prop) (x1 : Prop) := (x0 -> False) -> ((~ x1) = x0) -> x1.
Definition term203 (x0 : int) (x1 : int) := (x0 = x1) -> (x0 = x1) /\ (exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0)).
Definition term242 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) (x4 : Prop) := (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) = x3) -> (x3 -> ((rem x0 x1) = x2) = x4) -> (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2) = (x3 -> x4).
Definition term57 (x0 : int) (x1 : int) := (x0 = x1) /\ (exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0)).
Definition term213 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))) x1.
Definition term209 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = y0)) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) /\ (@eq2 int x0 y0 (int_mod x1))) x2).
Definition term228 (x0 : int) (x1 : int) := @eq2 int x0 (rem x0 x1) (int_mod x1).
Definition term80 (x0 : int) (x1 : int) (x2 : int) := @eq int (int_sub (int_sub x0 x1) (int_mul (int_of_num (NUMERAL 0)) x2)).
Definition term167 (x0 : int) (x1 : int) := int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))).
Definition term170 (x0 : int) (x1 : int) := int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term182 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x0) (int_add x1 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term98 (x0 : int) := ~ (forall y0 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0))).
Definition term55 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0).
Definition term171 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL 0)))).
Definition term66 (x0 : int) (x1 : int) := @eq int (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term48 (x0 : int) (x1 : int) := (x0 = x1) \/ False.
Definition term130 := ~ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term222 (x0 : int) (x1 : int) := or ((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = (rem x0 x1))).
Definition term78 (x0 : int) (x1 : int) := int_add (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term158 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((x0 = x2) /\ (~ (x1 = y0))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) x1)) = (int_add x2 (int_mul (int_of_num (NUMERAL (BIT1 0))) y0))).
Definition term143 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := forall y0 : int, ((x0 = x2) /\ (~ (x1 = y0))) -> ~ ((int_add x0 (int_mul x3 x1)) = (int_add x2 (int_mul x3 y0))).
Definition term72 (x0 : int) (x1 : int) := int_sub (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term258 := forall y0 : int, forall y1 : int, forall y2 : int, ((rem y0 y1) = y2) = ((((y1 = (int_of_num (NUMERAL 0))) /\ (y0 = y2)) \/ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) /\ (@eq2 int y0 y2 (int_mod y1))).
Definition term257 (x0 : int) := forall y0 : int, forall y1 : int, ((rem x0 y0) = y1) = ((((y0 = (int_of_num (NUMERAL 0))) /\ (x0 = y1)) \/ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) /\ (@eq2 int x0 y1 (int_mod y0))).
Definition term156 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x0 = x1) /\ (~ (y0 = y1))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y0)) = (int_add x1 (int_mul (int_of_num (NUMERAL (BIT1 0))) y1))).
Definition term154 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = y0) /\ (~ (y1 = y2))) -> ~ ((int_add x0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y1)) = (int_add y0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y2))).
Definition term152 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y2)) = (int_add y1 (int_mul (int_of_num (NUMERAL (BIT1 0))) y3))).
Definition term146 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul x0 y2)) = (int_add y1 (int_mul x0 y3))).
Definition term145 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = y0) /\ (~ (y1 = y2))) -> ~ ((int_add x0 (int_mul x1 y1)) = (int_add y0 (int_mul x1 y2))).
Definition term144 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, forall y1 : int, ((x0 = x1) /\ (~ (y0 = y1))) -> ~ ((int_add x0 (int_mul x2 y0)) = (int_add x1 (int_mul x2 y1))).
Definition term137 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, forall y1 : int, (~ (x2 = (int_of_num (NUMERAL 0)))) -> ((x0 = x1) /\ (~ (y0 = y1))) -> ~ ((int_add x0 (int_mul x2 y0)) = (int_add x1 (int_mul x2 y1))).
Definition term135 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, forall y2 : int, (~ (x1 = (int_of_num (NUMERAL 0)))) -> ((x0 = y0) /\ (~ (y1 = y2))) -> ~ ((int_add x0 (int_mul x1 y1)) = (int_add y0 (int_mul x1 y2))).
Definition term133 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) -> ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul x0 y2)) = (int_add y1 (int_mul x0 y3))).
Definition term131 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, forall y4 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((int_add y1 (int_mul y0 y3)) = (int_add y2 (int_mul y0 y4))).
Definition term92 := forall y0 : int, forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)).
Definition term12 := forall y0 : int, forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2)).
Definition term11 := forall y0 : int, forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term8 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1)).
Definition term7 (x0 : int) := forall y0 : int, forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term62 (x0 : int) (x1 : int) := @eq int (int_sub x0 x1).
Definition term68 (x0 : int) (x1 : int) := ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)).
Definition term180 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))))).
Definition term63 (x0 : int) (x1 : int) := @eq int (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term128 := S (Nat.add 0 0).
Definition term95 (x0 : int) (x1 : int) := ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)))).
Definition term240 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := forall y0 : Prop, (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) = x3) -> (x3 -> ((rem x0 x1) = x2) = y0) -> (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2) = (x3 -> y0).
Definition term236 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term124 (x0 : int) (x1 : int) := int_add (int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term0 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term188 := int_mul (int_add (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : int) (x1 : int) := imp (x0 = x1).
Definition term33 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((rem x0 x1) = x2).
Definition term113 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x1)) /\ (~ (x2 = x3)).
Definition term238 (x0 : int) (x1 : int) (x2 : int) := forall y0 : Prop, forall y1 : Prop, (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) = y0) -> (y0 -> ((rem x0 x1) = x2) = y1) -> (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2) = (y0 -> y1).
Definition term237 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term186 (x0 : nat) := int_add (int_neg (int_of_num x0)) (int_of_num x0).
Definition term224 (x0 : int) (x1 : int) := and (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)).
Definition term86 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term23 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term111 (x0 : int) (x1 : int) := ~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))).
Definition term104 (x0 : int) := exists y0 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0)))).
Definition term32 (x0 : int) (x1 : int) := @eq int (rem x0 x1).
Definition term147 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul x0 y2)) = (int_add y1 (int_mul x0 y3))).
Definition term93 := ~ (forall y0 : int, forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))).
Definition term241 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) = x3) -> (x3 -> ((rem x0 x1) = x2) = y0) -> (((((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = x2)) \/ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x1)))) /\ (@eq2 int x0 x2 (int_mod x1))) -> (rem x0 x1) = x2) = (x3 -> y0)) x4.
Definition term190 (x0 : int) := int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term101 (x0 : int) (x1 : int) := ~ ((fun y0 : int => ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0))) x1).
Definition term61 (x0 : int) := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term44 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term85 (x0 : int) (x1 : int) := ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) -> exists y0 : int, (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)).
Definition term184 (x0 : int) := int_mul (int_add (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term246 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2)).
Definition term84 (x0 : int) (x1 : int) := (x1 = x0) -> exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0).
Definition term233 (x0 : int) (x1 : int) := (fun y0 : int => ((rem x0 y0) = x0) = ((y0 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs y0))))) x1.
Definition term25 (x0 : int) := forall y0 : int, ~ ((int_le x0 y0) /\ (int_lt y0 x0)).
Definition term208 (x0 : int) (x1 : int) := (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = (rem x0 x1))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))) /\ (@eq2 int x0 (rem x0 x1) (int_mod x1)).
Definition term29 (x0 : int) (x1 : int) := (int_le x1 x0) /\ (int_lt x0 x1).
Definition term76 := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term165 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term230 (x0 : int) (x1 : int) (x2 : int) := ((rem x0 x2) = x1) -> (((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2)).
Definition term70 (x0 : int) (x1 : int) (x2 : int) := int_sub (int_sub x0 x1) (int_mul (int_of_num (NUMERAL 0)) x2).
Definition term114 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((int_add (int_mul x0 x3) (int_mul x2 x1)) = (int_add (int_mul x0 x1) (int_mul x2 x3))).
Definition term166 (x0 : int) (x1 : int) := int_mul (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) (int_of_num (NUMERAL 0)).
Definition term202 := ((~ (forall y0 : int, forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)))) = (exists y0 : int, exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)))))) -> forall y0 : int, forall y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) -> (int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)).
Definition term244 (x0 : int) (x1 : int) := False \/ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs x1))).
Definition term194 (x0 : int) (x1 : int) := (((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))))) -> False.
Definition term177 (x0 : int) (x1 : int) := int_add (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term200 (x0 : Prop) := ((exists y0 : int, exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))))) -> False) -> ((~ x0) = (exists y0 : int, exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)))))) -> x0.
Definition term245 (x0 : int) (x1 : int) := and ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_lt x0 (int_abs x1))).
Definition term31 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term216 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term220 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) /\ (x0 = (rem x0 x1)).
Definition term243 (x0 : int) (x1 : int) := False /\ (x0 = x1).
Definition term205 (x0 : int) (x1 : int) := fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = y0)) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) /\ (@eq2 int x0 y0 (int_mod x1)).
Definition term118 (x0 : int) (x1 : int) := int_mul (int_of_num (NUMERAL 0)) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term197 (x0 : int) (x1 : int) := ((((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))))) = False) -> ~ (((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))))).
Definition term229 (x0 : int) (x1 : int) := True /\ (@eq2 int x0 (rem x0 x1) (int_mod x1)).
Definition term36 (x0 : int) := and (x0 = (int_of_num (NUMERAL 0))).
Definition term105 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1) y2) = (int_of_num (NUMERAL 0))) -> (int_add y1 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y2)) = (int_of_num (NUMERAL 0))) y0).
Definition term99 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y1) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0))) y0).
Definition term89 (x0 : int) := fun y0 : int => ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0)).
Definition term119 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term34 (x0 : int) (x1 : int) := @eq Prop (x0 = x1).
Definition term20 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term103 (x0 : int) := fun y0 : int => ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0)))).
Definition term110 := exists y0 : int, exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)))).
Definition term210 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2))).
Definition term30 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term221 (x0 : int) (x1 : int) := False /\ (x0 = (rem x0 x1)).
Definition term14 (x0 : int) := forall y0 : int, (rem (rem x0 y0) y0) = (rem x0 y0).
Definition term125 (x0 : int) (x1 : int) := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) (int_mul (int_of_num (NUMERAL (BIT1 0))) (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term249 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term151 := (~ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0)))) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((int_add y0 (int_mul (int_of_num (NUMERAL (BIT1 0))) y2)) = (int_add y1 (int_mul (int_of_num (NUMERAL (BIT1 0))) y3))).
Definition term217 (x0 : int) (x1 : int) := int_lt (rem x0 x1) (int_abs x1).
Definition term52 (x0 : int) (x1 : int) := @eq2 int x0 x1 (int_mod (int_of_num (NUMERAL 0))).
Definition term227 (x0 : int) (x1 : int) := and (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = (rem x0 x1))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term117 := int_mul (int_of_num (NUMERAL 0)).
Definition term250 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term40 (x0 : int) (x1 : int) := or (x0 = x1).
Definition term59 (x0 : int) (x1 : int) := int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term90 (x0 : int) := forall y0 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) y0) = (int_of_num (NUMERAL 0))) -> (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0)) = (int_of_num (NUMERAL 0)).
Definition term109 := fun y0 : int => exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)))).
Definition term196 (x0 : int) (x1 : int) := (~ (((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0)))))) -> (((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)) = (int_of_num (NUMERAL 0))))) = False.
Definition term193 := (~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)))) -> ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) = False.
Definition term60 (x0 : int) (x1 : int) := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term201 (x0 : Prop) := ((~ x0) = (exists y0 : int, exists y1 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y0) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((int_add y0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1)) = (int_of_num (NUMERAL 0)))))) -> x0.
Definition term129 := (((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))) = False) -> ~ ((int_of_num (NUMERAL (BIT1 0))) = (int_of_num (NUMERAL 0))).
Definition term116 := int_of_num (NUMERAL (BIT1 0)).
Definition term28 (x0 : int) (x1 : int) := (~ ((int_le x1 x0) /\ (int_lt x0 x1))) -> ((int_le x1 x0) /\ (int_lt x0 x1)) = False.
Definition term254 (x0 : int) (x1 : int) (x2 : int) := (((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2))) /\ ((rem x0 x2) = (rem x1 x2))) -> True.
Definition term87 (x0 : Prop) := exists y0 : int, x0.
Definition term204 (x0 : int) (x1 : int) := ((x0 = x1) -> (x0 = x1) /\ (exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0))) /\ (((x0 = x1) /\ (exists y0 : int, (int_sub x0 x1) = (int_mul (int_of_num (NUMERAL 0)) y0))) -> x0 = x1).
Definition term77 := NUMERAL (BIT1 0).
Definition term53 (x0 : int) (x1 : int) (x2 : int) := (((x2 = (int_of_num (NUMERAL 0))) /\ (x0 = x1)) \/ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_lt x1 (int_abs x2)))) /\ (@eq2 int x0 x1 (int_mod x2)).
Definition term206 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = y0)) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) /\ (@eq2 int x0 y0 (int_mod x1))) x2.
Definition term75 (x0 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0)).
Definition term207 (x0 : int) (x1 : int) := (fun y0 : int => (((x1 = (int_of_num (NUMERAL 0))) /\ (x0 = y0)) \/ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x1)))) /\ (@eq2 int x0 y0 (int_mod x1))) (rem x0 x1).
Definition term108 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, ((int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y1) y2) = (int_of_num (NUMERAL 0))) -> (int_add y1 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y2)) = (int_of_num (NUMERAL 0))) y0).
Definition term181 (x0 : int) (x1 : int) := int_add (int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0) x1) (int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x1)).
