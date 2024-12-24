Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int (rem x0 y0) x1 (int_mod y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (@eq2 int (rem x0 y1) y0 (int_mod y1)) = (@eq2 int x0 y0 (int_mod y1))) x1.
Definition term56 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term55 (x0 : int -> Prop) := ~ (all x0).
Definition term40 (x0 : int) (x1 : int) := @eq int (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)).
Definition term34 (x0 : int) := int_sub (int_sub x0 x0).
Definition term50 (x0 : int) (x1 : int) := @eq int (int_sub (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)) (int_of_num (NUMERAL 0))).
Definition term12 (x0 : int) := forall y0 : int, @eq2 int x0 x0 (int_mod y0).
Definition term23 := int_of_num (NUMERAL 0).
Definition term7 (x0 : int) (x1 : int) := @eq2 int (rem x0 x1) x0 (int_mod x1).
Definition term38 (x0 : int) (x1 : int) := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1).
Definition term51 (x0 : int) := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0).
Definition term59 (x0 : int) := ~ ((fun y0 : int => (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))) x0).
Definition term39 (x0 : int) (x1 : int) (x2 : int) := @eq int (int_sub (int_sub x0 x0) (int_mul x1 x2)).
Definition term24 (x0 : int) (x1 : int) (x2 : int) := int_sub (int_sub x0 x0) (int_mul x1 x2).
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int (rem y0 y2) y1 (int_mod y2)) = (@eq2 int y0 y1 (int_mod y2))) x0.
Definition term61 := fun y0 : int => ~ ((fun y1 : int => (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y1)) = (int_of_num (NUMERAL 0))) y0).
Definition term63 := exists y0 : int, ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))).
Definition term66 := @eq int (int_of_num (NUMERAL 0)).
Definition term11 (x0 : int) := forall y0 : int, @eq2 int (rem x0 y0) x0 (int_mod y0).
Definition term67 := ~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))).
Definition term77 := ((~ (forall y0 : int, (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0)))) = (exists y0 : int, ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))))) -> forall y0 : int, (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0)).
Definition term33 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) x0.
Definition term14 := fun y0 : int => forall y1 : int, @eq2 int y0 y0 (int_mod y1).
Definition term13 := fun y0 : int => forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1).
Definition term37 (x0 : int) (x1 : int) := int_add (int_of_num (NUMERAL 0)) (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)).
Definition term58 (x0 : int) := (fun y0 : int => (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))) x0.
Definition term10 (x0 : int) := fun y0 : int => @eq2 int x0 x0 (int_mod y0).
Definition term29 := int_add (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0))).
Definition term27 := int_neg (int_of_num (NUMERAL (BIT1 0))).
Definition term43 (x0 : int) := exists y0 : int, (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x0)) = (int_of_num (NUMERAL 0)).
Definition term74 (x0 : Prop) (x1 : Prop) := (x0 -> False) -> ((~ x1) = x0) -> x1.
Definition term35 := int_sub (int_of_num (NUMERAL 0)).
Definition term53 := forall y0 : int, (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0)).
Definition term21 := fun y0 : int => forall y1 : int, exists y2 : int, (int_sub y0 y0) = (int_mul y1 y2).
Definition term54 := ~ (forall y0 : int, (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) (x1 : int) := exists y0 : int, (int_sub x0 x0) = (int_mul x1 y0).
Definition term17 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0).
Definition term65 (x0 : int) := @eq int (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)).
Definition term22 := forall y0 : int, forall y1 : int, exists y2 : int, (int_sub y0 y0) = (int_mul y1 y2).
Definition term16 := forall y0 : int, forall y1 : int, @eq2 int y0 y0 (int_mod y1).
Definition term15 := forall y0 : int, forall y1 : int, @eq2 int (rem y0 y1) y0 (int_mod y1).
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int (rem x0 y1) y0 (int_mod y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term60 (x0 : int) := ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0))).
Definition term44 (x0 : int) (x1 : int) := int_sub (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)) (int_of_num (NUMERAL 0)).
Definition term48 (x0 : int) (x1 : int) := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term49 (x0 : int) (x1 : int) := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)) (int_of_num (NUMERAL 0)).
Definition term31 := int_mul (int_add (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : nat) := int_add (int_neg (int_of_num x0)) (int_of_num x0).
Definition term25 (x0 : int) := int_add x0 (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term72 (x0 : int) := ((~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0)))) = False) -> ~ (~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0)))).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := @eq2 int (rem x0 x2) x1 (int_mod x2).
Definition term26 (x0 : int) := int_mul (int_add (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term64 := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))).
Definition term70 (x0 : int) := ~ (~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0)))).
Definition term69 (x0 : int) := (~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0)))) -> False.
Definition term71 (x0 : int) := (~ (~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0))))) -> (~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) x0)) = (int_of_num (NUMERAL 0)))) = False.
Definition term9 (x0 : int) := fun y0 : int => @eq2 int (rem x0 y0) x0 (int_mod y0).
Definition term47 := int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term19 (x0 : int) := fun y0 : int => exists y1 : int, (int_sub x0 x0) = (int_mul y0 y1).
Definition term8 (x0 : int) (x1 : int) := @eq2 int x0 x0 (int_mod x1).
Definition term52 := fun y0 : int => (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0)).
Definition term42 (x0 : int) := fun y0 : int => (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x0)) = (int_of_num (NUMERAL 0)).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (@eq2 int (rem x0 y0) x1 (int_mod y0)) = (@eq2 int x0 x1 (int_mod y0))) x2.
Definition term75 (x0 : Prop) := ((exists y0 : int, ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0)))) -> False) -> ((~ x0) = (exists y0 : int, ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))))) -> x0.
Definition term20 (x0 : int) := forall y0 : int, exists y1 : int, (int_sub x0 x0) = (int_mul y0 y1).
Definition term57 := exists y0 : int, ~ ((fun y1 : int => (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y1)) = (int_of_num (NUMERAL 0))) y0).
Definition term36 (x0 : int) (x1 : int) := int_sub (int_of_num (NUMERAL 0)) (int_mul x0 x1).
Definition term73 := (exists y0 : int, ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0)))) -> False.
Definition term32 := int_mul (int_of_num (NUMERAL 0)).
Definition term41 (x0 : int) (x1 : int) := fun y0 : int => (int_sub x0 x0) = (int_mul x1 y0).
Definition term68 := (~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)))) -> ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) = False.
Definition term76 (x0 : Prop) := ((~ x0) = (exists y0 : int, ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))))) -> x0.
Definition term30 := NUMERAL (BIT1 0).
Definition term45 (x0 : int) (x1 : int) := int_add (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)) (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term62 := fun y0 : int => ~ ((int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (NUMERAL 0)) y0)) = (int_of_num (NUMERAL 0))).
Definition term46 (x0 : nat) := int_mul (int_neg (int_of_num x0)) (int_of_num (NUMERAL 0)).
