Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term248 := or (exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))).
Definition term88 (x0 : Prop) (x1 : Prop) (x2 : Prop) := and ((False -> x0) /\ (x1 -> x2)).
Definition term42 (x0 : Prop) (x1 : Prop) (x2 : Prop) := and ((True -> x0) /\ (x1 -> x2)).
Definition term532 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term717 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term714 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term442 (x0 : int) := fun y0 : int => ((~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) /\ ((rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0))).
Definition term263 (x0 : int) (x1 : int) := (fun y0 : int => ~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)))) x1.
Definition term447 (x0 : int) := int_mul x0 (int_of_num (NUMERAL 0)).
Definition term444 := fun y0 : int => forall y1 : int, ((~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ ((rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term381 (x0 : int) (x1 : int) (x2 : int) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term656 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (((y0 -> x0) /\ (x1 -> x2)) /\ (y0 /\ x1)) -> (y0 /\ x0) /\ (x1 /\ x2)) False.
Definition term457 (x0 : int) := False -> (div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) = x0.
Definition term78 (x0 : Prop) := imp ((True -> x0) /\ True).
Definition term731 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term288 := exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (rem (int_mul y3 y4) y4) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))))) y0.
Definition term284 := exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0.
Definition term253 := exists y0 : int, (fun y1 : int => exists y2 : int, ~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0)))) y0.
Definition term226 := exists y0 : int, (fun y1 : int => exists y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2))) y0.
Definition term154 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term740 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term555 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term583 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term153 (x0 : int -> Prop) := ~ (all x0).
Definition term386 := (~ False) -> False.
Definition term9 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = (int_add (int_mul x1 x3) x2)) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x3))).
Definition term594 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1)) x2.
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1)) x2.
Definition term384 (x0 : int) (x1 : int) := (~ ((div (int_mul x0 x1) x0) = x1)) -> (div (int_mul x0 x1) x0) = x1.
Definition term366 (x0 : int) (x1 : int) := (~ ((div (int_mul x1 x0) x0) = x1)) -> (div (int_mul x1 x0) x0) = x1.
Definition term369 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term686 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))))).
Definition term397 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x0 = x2) /\ (x1 = x3)) -> (rem x0 x1) = (rem x2 x3).
Definition term21 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term512 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term96 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((((x0 -> x1) /\ (x2 -> x3)) /\ (x0 /\ x2)) -> (x0 /\ x1) /\ (x2 /\ x3)) -> (x0 /\ x1) /\ (x2 /\ x3).
Definition term639 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term157 (x0 : int) (x1 : int) := (fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) x0) = y0) x1.
Definition term405 (x0 : int) (x1 : int) := (~ ((rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0)))) -> (rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0)).
Definition term401 (x0 : int) (x1 : int) := (~ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0)))) -> (rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0)).
Definition term627 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term436 (x0 : int) := @eq Prop ((forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) /\ (forall y0 : int, (rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0)))).
Definition term435 (x0 : int) := @eq Prop ((forall y0 : int, (fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0) /\ (forall y0 : int, (fun y1 : int => (rem (int_mul x0 y1) y1) = (int_of_num (NUMERAL 0))) y0)).
Definition term419 := @eq Prop ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0)))).
Definition term418 := @eq Prop ((forall y0 : int, (fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) y0)).
Definition term646 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term344 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (div x0 x1) = (div x2 x3).
Definition term696 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term611 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term647 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term131 (x0 : int) := forall y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) x0) = y0.
Definition term271 (x0 : int) := fun y0 : int => (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)))).
Definition term676 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))).
Definition term582 (x0 : nat) := real_neg (real_of_num x0).
Definition term605 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term780 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term502 := real_of_int (int_of_num (NUMERAL 0)).
Definition term350 (x0 : Prop) := ~ (~ x0).
Definition term503 := real_of_num (NUMERAL 0).
Definition term533 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))).
Definition term462 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term161 (x0 : int) := exists y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)).
Definition term326 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x1 = x3)) \/ ((div x0 x1) = (div x2 x3)).
Definition term388 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x1 = x3)) \/ ((rem x0 x1) = (rem x2 x3)).
Definition term32 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (((y0 -> x0) /\ (x1 -> x2)) /\ (y0 /\ x1)) -> (y0 /\ x0) /\ (x1 /\ x2)) True.
Definition term278 (x0 : int -> Prop) (x1 : int -> Prop) := (exists y0 : int, x0 y0) \/ (exists y0 : int, x1 y0).
Definition term486 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term570 (x0 : int) (x1 : int) := ((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0)))).
Definition term509 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term522 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))).
Definition term207 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((fun y0 : int => ~ ((div (int_mul x0 y0) x0) = y0)) x1).
Definition term31 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((y0 -> x0) /\ (x1 -> x2)) /\ (y0 /\ x1)) -> (y0 /\ x0) /\ (x1 /\ x2)) x3.
Definition term20 := int_of_num (NUMERAL 0).
Definition term61 (x0 : Prop) (x1 : Prop) := and (True /\ (x0 -> x1)).
Definition term323 (x0 : int) (x1 : int) := (fun y0 : int => (rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0))) x1.
Definition term556 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term483 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term677 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0)).
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2)) x1.
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2)) x1.
Definition term349 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term219 := ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (exists y1 : int, ~ ((div (int_mul y0 y1) y0) = y1)))) \/ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term196 := ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term527 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term783 (x0 : int) (x1 : int) := ((~ (~ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) /\ (((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0)))))))) -> False) -> ~ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) /\ (((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term232 := fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ (exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))).
Definition term645 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term649 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term608 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term377 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term395 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop (((rem x0 x2) = (rem x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term342 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop (((div x0 x2) = (div x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term759 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term276 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term727 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term771 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term109 := (((~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term295 := fun y0 : int => ((fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0) \/ ((fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (rem (int_mul y3 y4) y4) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))))) y0).
Definition term710 (x0 : int) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term236 (x0 : int) (x1 : int) := (fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0))) x1.
Definition term193 := or (~ ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1)).
Definition term546 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term411 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) x0.
Definition term322 (x0 : int) := (fun y0 : int => forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) x0.
Definition term320 (x0 : int) := (fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) x0.
Definition term318 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) x0.
Definition term184 (x0 : int) := (fun y0 : int => forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term164 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) x0.
Definition term756 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term353 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term95 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 /\ x1) /\ (x2 /\ x3).
Definition term106 := ~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term482 (x0 : int) (x1 : int) := ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1))).
Definition term588 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term197 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term103 (x0 : Prop) := (~ x0) -> False.
Definition term685 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))))).
Definition term379 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term355 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term548 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term566 := or (~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))).
Definition term610 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term634 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False /\ x0) /\ (x1 /\ x2).
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3)) x0.
Definition term1 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) x0.
Definition term378 (x0 : int) (x1 : int) (x2 : int) := (x1 = x0) /\ (x1 = x2).
Definition term105 := (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> False.
Definition term491 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term134 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0.
Definition term620 (x0 : int) (x1 : int) := real_sub (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))).
Definition term681 (x0 : int) := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term243 (x0 : int) := fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1))) y0).
Definition term616 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term179 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))) y0).
Definition term159 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) x0) = y1) y0).
Definition term82 (x0 : Prop) (x1 : Prop) := and (False /\ (x0 -> x1)).
Definition term709 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term679 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))).
Definition term41 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 -> x2).
Definition term365 (x0 : int) (x1 : int) := @eq Prop ((x0 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul x1 x0) x0) = x1)).
Definition term189 := and (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term170 := and (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)).
Definition term169 := and (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0).
Definition term57 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((x0 /\ (x1 -> x2)) /\ x1) -> x0 /\ (x1 /\ x2)).
Definition term481 (x0 : int) (x1 : int) := ~ ((~ (x1 = (int_of_num (NUMERAL 0)))) -> ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1)))).
Definition term618 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term514 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term181 (x0 : int) := exists y0 : int, ~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))).
Definition term732 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term683 (x0 : int) := ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))).
Definition term643 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term638 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term578 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0).
Definition term52 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((y0 /\ (x0 -> x1)) /\ x0) -> y0 /\ (x0 /\ x1).
Definition term427 (x0 : int) := (forall y0 : int, (fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0) /\ (forall y0 : int, (fun y1 : int => (rem (int_mul x0 y1) y1) = (int_of_num (NUMERAL 0))) y0).
Definition term409 := (forall y0 : int, (fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) y0).
Definition term343 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term655 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term180 (x0 : int) := fun y0 : int => ~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))).
Definition term387 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x1 = x3) -> (rem x0 x1) = (rem x2 x3).
Definition term324 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x1 = x3) -> (div x0 x1) = (div x2 x3).
Definition term151 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 x1) x0) = x1)).
Definition term67 (x0 : Prop) (x1 : Prop) := True /\ (x0 /\ x1).
Definition term423 (x0 : int) := (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) /\ (forall y0 : int, (rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0))).
Definition term633 (x0 : int) (x1 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term518 (x0 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term691 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term766 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term748 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term450 := @eq int (int_of_num (NUMERAL 0)).
Definition term86 (x0 : Prop) := and (False -> x0).
Definition term625 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term707 (x0 : int) := real_ge (real_of_int x0).
Definition term198 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term354 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = x1) /\ (x2 = x3).
Definition term547 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0))))).
Definition term214 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (exists y0 : int, ~ ((div (int_mul x0 y0) x0) = y0)).
Definition term360 (x0 : int) (x1 : int) := (~ ((div (int_mul x0 x1) x1) = (div (int_mul x1 x0) x1))) -> (div (int_mul x0 x1) x1) = (div (int_mul x1 x0) x1).
Definition term241 (x0 : int) (x1 : int) := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ ((fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0))) x1).
Definition term59 (x0 : Prop) (x1 : Prop) := ((False /\ (x0 -> x1)) /\ x0) -> False /\ (x0 /\ x1).
Definition term145 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul x1 x0) x0) = x1).
Definition term604 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term332 (x0 : Prop) := (~ x0) -> x0.
Definition term215 := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (exists y1 : int, ~ ((div (int_mul y0 y1) y0) = y1)).
Definition term598 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term560 (x0 : int) := real_le (real_of_int (int_abs x0)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term356 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term331 (x0 : int) (x1 : int) := ~ ((int_mul x1 x0) = (int_mul x0 x1)).
Definition term551 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term565 (x0 : int) := real_le (real_abs (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term46 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (((True -> x0) /\ (x2 -> x1)) /\ (True /\ x2)).
Definition term124 (x0 : int) := fun y0 : int => (rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0)).
Definition term300 (x0 : int) (x1 : int) := (fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) x1.
Definition term584 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term195 := (~ ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1)) \/ (~ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term375 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term554 := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term720 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))).
Definition term469 (x0 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x0))).
Definition term719 (x0 : int) := or ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))).
Definition term524 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term544 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))).
Definition term455 (x0 : int) (x1 : int) := @eq int (div (int_mul x0 x1) x1).
Definition term724 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term670 := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term347 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term185 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))) x0).
Definition term165 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) x0).
Definition term602 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term309 (x0 : int) (x1 : int) := or ((fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) x1).
Definition term372 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term641 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term472 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term492 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term558 (x0 : int) := ~ (int_lt (int_of_num (NUMERAL 0)) (int_abs x0)).
Definition term721 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))))).
Definition term477 (x0 : int) (x1 : int) := int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)).
Definition term726 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : Prop) (x1 : Prop) := imp ((False /\ (x1 -> x0)) /\ x1).
Definition term65 (x0 : Prop) (x1 : Prop) := imp ((True /\ (x1 -> x0)) /\ x1).
Definition term373 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term36 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((((x0 -> x1) /\ (x2 -> x3)) /\ (x0 /\ x2)) -> (x0 /\ x1) /\ (x2 /\ x3)).
Definition term550 (x0 : int) (x1 : int) := (real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term403 (x0 : int) (x1 : int) := ((rem (int_mul x0 x1) x1) = (rem (int_mul x1 x0) x1)) /\ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0))).
Definition term621 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_of_int x1)).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term286 (x0 : int) := (fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) x0.
Definition term282 (x0 : int) := (fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) x0.
Definition term224 (x0 : int) := (fun y0 : int => exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))) x0.
Definition term464 (x0 : int) (x1 : int) := and ((div (int_mul x1 x0) x0) = x1).
Definition term674 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term304 (x0 : int) (x1 : int) := (fun y0 : int => (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))))) x1.
Definition term561 (x0 : int) := real_of_int (int_abs x0).
Definition term521 (x0 : int) (x1 : int) := int_le (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))).
Definition term730 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term396 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (rem x0 x1) = (rem x2 x3).
Definition term628 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term644 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term637 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term615 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term515 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term133 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x1 x0) x0) = x1.
Definition term129 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 x1) x0) = x1.
Definition term736 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term723 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term339 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term146 (x0 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul x0 y0) y0) = x0).
Definition term528 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 x1)).
Definition term62 (x0 : Prop) (x1 : Prop) := and (x0 -> x1).
Definition term126 := fun y0 : int => forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0)).
Definition term122 := fun y0 : int => forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)).
Definition term92 (x0 : Prop) := and (False /\ x0).
Definition term87 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (False -> x0) /\ (x1 -> x2).
Definition term725 := real_le (real_of_num (NUMERAL 0)).
Definition term553 := ~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term489 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term160 (x0 : int) := fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)).
Definition term733 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term393 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((rem x0 x2) = (rem x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term340 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((div x0 x2) = (div x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term507 (x0 : int) := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term715 (x0 : int) := and (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term712 (x0 : int) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term296 := fun y0 : int => (exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ (exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term479 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ (~ (((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1))))).
Definition term417 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term617 (x0 : int) := or (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term575 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term769 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term420 (x0 : int) := and ((fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) x0).
Definition term43 (x0 : Prop) (x1 : Prop) (x2 : Prop) := and (x0 /\ (x1 -> x2)).
Definition term389 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = x2) -> (~ (x1 = x3)) \/ ((rem x0 x1) = (rem x2 x3)).
Definition term327 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = x2) -> (~ (x1 = x3)) \/ ((div x0 x1) = (div x2 x3)).
Definition term70 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) x1.
Definition term738 := real_lt (real_of_num (NUMERAL 0)).
Definition term297 := exists y0 : int, (exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ (exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term438 (x0 : int) (x1 : int) := and ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x1 x0) x0) = x1).
Definition term139 := and ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1).
Definition term432 (x0 : int) := and (forall y0 : int, (fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0).
Definition term414 := and (forall y0 : int, (fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0).
Definition term498 (x0 : int) := real_add (real_of_int x0).
Definition term262 (x0 : int) := exists y0 : int, (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ ((fun y1 : int => ~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0)))) y0).
Definition term250 := exists y0 : int, (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ ((fun y1 : int => exists y2 : int, ~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0)))) y0).
Definition term235 (x0 : int) := exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1))) y0).
Definition term223 := exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((fun y1 : int => exists y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2))) y0).
Definition term144 (x0 : int) (x1 : int) := (~ (~ (x0 = (int_of_num (NUMERAL 0))))) \/ ((div (int_mul x1 x0) x0) = x1).
Definition term107 := (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term45 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ (x2 -> x1)) /\ x2.
Definition term399 (x0 : int) (x1 : int) := (~ ((rem (int_mul x0 x1) x1) = (rem (int_mul x1 x0) x1))) -> (rem (int_mul x0 x1) x1) = (rem (int_mul x1 x0) x1).
Definition term777 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term716 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term713 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term573 (x0 : int) (x1 : int) := ~ (~ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) /\ (((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0))))))).
Definition term693 (x0 : int) := or (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term658 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))).
Definition term265 (x0 : int) := exists y0 : int, (fun y1 : int => ~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0)))) y0.
Definition term212 (x0 : int) := exists y0 : int, (fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0.
Definition term779 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term329 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term49 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True /\ x0) /\ (x1 /\ x2).
Definition term119 (x0 : int) (x1 : int) := rem (int_mul x1 x0) x1.
Definition term722 (x0 : int) := ((((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) \/ ((((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))))).
Definition term701 (x0 : int) := ((((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) \/ ((((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))))).
Definition term567 := or (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term506 (x0 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term735 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term50 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 /\ x2).
Definition term468 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1))).
Definition term761 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term319 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul x0 y0) = (int_mul y0 x0)) x1.
Definition term494 (x0 : nat) := real_of_int (int_of_num x0).
Definition term475 (x0 : int) (x1 : int) := (~ ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) \/ (~ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1)))).
Definition term652 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term260 := exists y0 : int, (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term233 := exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ (exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))).
Definition term111 := (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term382 (x0 : int) (x1 : int) := ((div (int_mul x1 x0) x0) = (div (int_mul x0 x1) x0)) /\ ((div (int_mul x1 x0) x0) = x1).
Definition term682 := or ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term648 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term595 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term334 (x0 : int) := ~ (x0 = x0).
Definition term552 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term465 (x0 : int) (x1 : int) := ((div (int_mul x0 x1) x1) = x0) /\ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0))).
Definition term75 (x0 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) False.
Definition term490 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term218 := or ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (exists y1 : int, ~ ((div (int_mul y0 y1) y0) = y1)))).
Definition term194 := or ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))).
Definition term76 (x0 : Prop) := ((False -> x0) /\ False) -> False /\ x0.
Definition term487 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term635 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term510 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term208 (x0 : int) := fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0).
Definition term275 := (exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ (exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term664 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term734 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term599 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term669 := real_sub (real_of_num (NUMERAL 0)).
Definition term631 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term298 (x0 : int) := (exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0) \/ (exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))))) y0).
Definition term280 := (exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0) \/ (exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (rem (int_mul y3 y4) y4) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))))) y0).
Definition term314 (x0 : int) := fun y0 : int => ((forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) \/ ((forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))))).
Definition term257 (x0 : int) := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, ~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)))).
Definition term640 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term606 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term71 (x0 : Prop) := (fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) True.
Definition term624 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term700 (x0 : int) := or ((((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term539 (x0 : int) (x1 : int) := int_le (int_add (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1).
Definition term305 (x0 : int) := fun y0 : int => (fun y1 : int => (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))))) y0.
Definition term237 (x0 : int) := fun y0 : int => (fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1))) y0.
Definition term571 (x0 : int) := and ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term657 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term760 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term117 (x0 : int) := forall y0 : int, (int_mul x0 y0) = (int_mul y0 x0).
Definition term74 (x0 : Prop) (x1 : Prop) := @eq Prop (((x0 -> x1) /\ x0) -> x0 /\ x1).
Definition term210 (x0 : int) := @eq Prop (exists y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0))).
Definition term209 (x0 : int) := @eq Prop (exists y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0)).
Definition term258 := fun y0 : int => (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ ((fun y1 : int => exists y2 : int, ~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0)))) y0).
Definition term231 := fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((fun y1 : int => exists y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2))) y0).
Definition term428 (x0 : int) := forall y0 : int, ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0) /\ ((fun y1 : int => (rem (int_mul x0 y1) y1) = (int_of_num (NUMERAL 0))) y0).
Definition term410 := forall y0 : int, ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0) /\ ((fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) y0).
Definition term346 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term660 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term459 := rem (int_of_num (NUMERAL 0)).
Definition term40 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (True -> x0) /\ (x1 -> x2).
Definition term718 (x0 : int) := or ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))).
Definition term294 (x0 : int) := (exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) \/ (exists y0 : int, (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))))).
Definition term501 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term358 (x0 : int) (x1 : int) := ((int_mul x0 x1) = (int_mul x1 x0)) /\ (x1 = x1).
Definition term48 (x0 : Prop) := and (True /\ x0).
Definition term69 (x0 : Prop) := fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0.
Definition term572 (x0 : int) (x1 : int) := ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) /\ (((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0))))).
Definition term80 (x0 : Prop) := imp ((False -> x0) /\ False).
Definition term596 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term404 (x0 : int) (x1 : int) := (((rem (int_mul x0 x1) x1) = (rem (int_mul x1 x0) x1)) /\ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0)))) -> (rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0)).
Definition term385 (x0 : int) (x1 : int) := ((div (int_mul x0 x1) x0) = x1) -> False.
Definition term30 (x0 : Prop) (x1 : Prop) (x2 : Prop) := fun y0 : Prop => (((y0 -> x0) /\ (x1 -> x2)) /\ (y0 /\ x1)) -> (y0 /\ x0) /\ (x1 /\ x2).
Definition term505 (x0 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term549 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term663 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term619 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term55 (x0 : Prop) (x1 : Prop) := ((True /\ (x0 -> x1)) /\ x0) -> True /\ (x0 /\ x1).
Definition term765 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term708 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term174 (x0 : int) := ~ (forall y0 : int, (rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))).
Definition term155 (x0 : int) := ~ (forall y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) x0) = y0).
Definition term147 (x0 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul x0 y0) y0) = x0).
Definition term394 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((rem x0 x1) = (rem x2 x3)))).
Definition term341 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((div x0 x1) = (div x2 x3)))).
Definition term89 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((False -> x0) /\ (x2 -> x1)) /\ (False /\ x2).
Definition term199 (x0 : Prop) (x1 : int -> Prop) := exists y0 : int, x0 /\ (x1 y0).
Definition term269 (x0 : int) (x1 : int) := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0)))).
Definition term440 (x0 : int) (x1 : int) := ((~ (x1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 x1) x1) = x0) /\ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0))).
Definition term757 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term371 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term476 (x0 : int) (x1 : int) := ~ (((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1)))).
Definition term754 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term746 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term306 (x0 : int) := exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))))) y0.
Definition term302 (x0 : int) := exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0.
Definition term238 (x0 : int) := exists y0 : int, (fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1))) y0.
Definition term192 := ~ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))).
Definition term173 := ~ ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1).
Definition term517 (x0 : int) := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term68 (x0 : Prop) (x1 : Prop) := ((x0 -> x1) /\ x0) -> x0 /\ x1.
Definition term426 := forall y0 : int, (forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term443 (x0 : int) := forall y0 : int, ((~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) /\ ((rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0))).
Definition term600 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term622 (x0 : int) (x1 : int) := real_sub (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term312 (x0 : int) (x1 : int) := ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ ((~ (x1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x1 x0) x1) = x0)))) \/ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0))))).
Definition term541 (x0 : int) (x1 : int) := int_add (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0))).
Definition term672 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term374 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term613 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term478 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x0)).
Definition term120 (x0 : int) := fun y0 : int => (rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)).
Definition term775 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term83 (x0 : Prop) (x1 : Prop) := (False /\ (x1 -> x0)) /\ x1.
Definition term213 (x0 : int) := exists y0 : int, ~ ((div (int_mul x0 y0) x0) = y0).
Definition term445 := forall y0 : int, forall y1 : int, ((~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ ((rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term149 := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0).
Definition term113 := forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0).
Definition term102 := forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)).
Definition term101 := forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0)).
Definition term100 := forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1.
Definition term99 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0.
Definition term14 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term13 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2).
Definition term12 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1).
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1).
Definition term2 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2).
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3).
Definition term687 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))).
Definition term94 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x2 -> x0) /\ (x3 -> x1)) /\ (x2 /\ x3).
Definition term592 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term661 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term773 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term525 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term614 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term79 (x0 : Prop) := (False -> x0) /\ False.
Definition term678 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_abs (real_of_int x0))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term256 (x0 : int) := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ ((fun y0 : int => exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))) x0).
Definition term229 (x0 : int) := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ ((fun y0 : int => exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))) x0).
Definition term764 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)).
Definition term742 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term98 := ((((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))))) -> ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1)) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term729 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term367 (x0 : int) (x1 : int) := ~ ((div (int_mul x1 x0) x0) = x1).
Definition term205 (x0 : int) (x1 : int) := ~ ((div (int_mul x0 x1) x0) = x1).
Definition term488 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term81 (x0 : Prop) (x1 : Prop) := False /\ (x0 -> x1).
Definition term441 (x0 : int) := fun y0 : int => ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0) /\ ((fun y1 : int => (rem (int_mul x0 y1) y1) = (int_of_num (NUMERAL 0))) y0).
Definition term753 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term711 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term642 := S (Nat.add 0 0).
Definition term585 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term484 (x0 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) \/ (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term152 (x0 : int) (x1 : int) := div (int_mul x1 x0) x1.
Definition term330 (x0 : int) (x1 : int) := (~ ((int_mul x1 x0) = (int_mul x0 x1))) -> (int_mul x1 x0) = (int_mul x0 x1).
Definition term73 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 -> x0) /\ y0) -> y0 /\ x0) x1).
Definition term629 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term579 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term697 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term587 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term675 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_abs (real_of_int x0)).
Definition term559 (x0 : int) := int_le (int_abs x0) (int_of_num (NUMERAL 0)).
Definition term315 (x0 : int) := exists y0 : int, ((forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) \/ ((forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))))).
Definition term540 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_mul x0 x1)).
Definition term425 := fun y0 : int => (forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term463 (x0 : int) (x1 : int) := True -> (div (int_mul x1 x0) x0) = x1.
Definition term667 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term784 (x0 : int) (x1 : int) := ~ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) /\ (((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term148 := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0).
Definition term136 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0.
Definition term132 := fun y0 : int => forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1.
Definition term118 := fun y0 : int => forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0).
Definition term694 (x0 : int) := or (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term706 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term245 (x0 : int) := exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0))).
Definition term313 (x0 : int) := fun y0 : int => ((fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0) \/ ((fun y1 : int => (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))))) y0).
Definition term537 (x0 : int) (x1 : int) := or (int_le (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))).
Definition term673 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term745 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term665 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term362 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term370 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term774 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term623 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term85 (x0 : Prop) (x1 : Prop) := False /\ (x0 /\ x1).
Definition term508 (x0 : int) := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term150 (x0 : int) (x1 : int) := ~ ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 x1) x0) = x1).
Definition term538 (x0 : int) (x1 : int) := or (real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))).
Definition term29 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term650 := real_mul (real_of_num (NUMERAL 0)).
Definition term357 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x0 = x2) /\ (x1 = x3)) -> (div x0 x1) = (div x2 x3).
Definition term452 (x0 : int) (x1 : int) := div (int_mul x0 x1).
Definition term461 (x0 : int) (x1 : int) := @eq int (rem (int_mul x0 x1) x1).
Definition term123 (x0 : int) (x1 : int) := rem (int_mul x0 x1) x1.
Definition term352 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term688 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))).
Definition term416 := forall y0 : int, (fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) y0.
Definition term413 := forall y0 : int, (fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0.
Definition term668 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term574 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term22 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term138 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1.
Definition term128 := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)).
Definition term15 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term785 := (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0)))).
Definition term203 (x0 : int) := fun y0 : int => ~ ((div (int_mul x0 y0) x0) = y0).
Definition term535 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term272 (x0 : int) := exists y0 : int, (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)))).
Definition term500 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term268 (x0 : int) (x1 : int) := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ ((fun y0 : int => ~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)))) x1).
Definition term130 (x0 : int) := fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) x0) = y0.
Definition term270 (x0 : int) := fun y0 : int => (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ ((fun y1 : int => ~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0)))) y0).
Definition term261 (x0 : int) := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, (fun y1 : int => ~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0)))) y0).
Definition term249 := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, (fun y1 : int => exists y2 : int, ~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0)))) y0).
Definition term234 (x0 : int) := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1))) y0).
Definition term222 := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (fun y1 : int => exists y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2))) y0).
Definition term135 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0.
Definition term429 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) x1.
Definition term182 := ~ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))).
Definition term162 := ~ (forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1).
Definition term112 := ~ (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)).
Definition term473 (x0 : int) (x1 : int) := or (~ ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))))).
Definition term609 (x0 : int) := real_sub (real_of_int x0).
Definition term590 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term77 (x0 : Prop) := (True -> x0) /\ True.
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0)) x3.
Definition term654 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term437 (x0 : int) (x1 : int) := and ((fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) x1).
Definition term516 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term336 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term177 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))) x1).
Definition term158 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) x0) = y0) x1).
Definition term137 := imp (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0).
Definition term127 := imp (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))).
Definition term293 (x0 : int) := ((fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) x0) \/ ((fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) x0).
Definition term581 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term564 (x0 : int) := real_le (real_abs (real_of_int x0)).
Definition term470 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) \/ (~ (int_lt (int_of_num (NUMERAL 0)) (int_abs x0))).
Definition term201 (x0 : int) := exists y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0).
Definition term408 (x0 : int -> Prop) (x1 : int -> Prop) := forall y0 : int, (x0 y0) /\ (x1 y0).
Definition term632 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term778 (x0 : int) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term772 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term767 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term749 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term35 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x0 -> x1) /\ (x2 -> x3)) /\ (x0 /\ x2)) -> (x0 /\ x1) /\ (x2 /\ x3).
Definition term684 (x0 : int) := and ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term191 := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term172 := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))).
Definition term460 := rem (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term568 (x0 : int) := (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : Prop) (x1 : Prop) := (True /\ (x1 -> x0)) /\ x1.
Definition term612 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term264 (x0 : int) := fun y0 : int => (fun y1 : int => ~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0)))) y0.
Definition term211 (x0 : int) := fun y0 : int => (fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0.
Definition term392 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x1)) \/ (((rem x0 x2) = (rem x1 x3)) \/ (~ (x2 = x3))).
Definition term338 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x1)) \/ (((div x0 x2) = (div x1 x3)) \/ (~ (x2 = x3))).
Definition term597 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term115 := (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> ~ (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)).
Definition term361 (x0 : int) (x1 : int) := ~ ((div (int_mul x0 x1) x1) = (div (int_mul x1 x0) x1)).
Definition term230 (x0 : int) := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0))).
Definition term217 := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (exists y1 : int, ~ ((div (int_mul y0 y1) y0) = y1))).
Definition term421 (x0 : int) := and (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0).
Definition term114 := imp (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term480 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ ((~ ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) \/ (~ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1))))).
Definition term485 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term422 (x0 : int) := ((fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) x0) /\ ((fun y0 : int => forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) x0).
Definition term451 (x0 : int) := imp (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term703 (x0 : real) (x1 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term781 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term607 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term291 (x0 : int) := or ((fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) x0).
Definition term64 (x0 : Prop) (x1 : Prop) := (x1 -> x0) /\ x1.
Definition term108 := ((~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term569 (x0 : int) (x1 : int) := or ((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))).
Definition term504 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term8 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x1 = (int_add (int_mul x0 x2) x3)) /\ ((int_le (int_of_num (NUMERAL 0)) x3) /\ (int_lt x3 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term39 (x0 : Prop) := and (True -> x0).
Definition term279 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) \/ (x1 y0).
Definition term38 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((False -> x0) /\ (x1 -> x2)) /\ (False /\ x1)) -> (False /\ x0) /\ (x1 /\ x2).
Definition term33 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((True -> x0) /\ (x1 -> x2)) /\ (True /\ x1)) -> (True /\ x0) /\ (x1 /\ x2).
Definition term311 (x0 : int) (x1 : int) := ((fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) x1) \/ ((fun y0 : int => (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))))) x1).
Definition term141 (x0 : int) (x1 : int) := div (int_mul x0 x1) x1.
Definition term125 (x0 : int) := forall y0 : int, (rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0)).
Definition term121 (x0 : int) := forall y0 : int, (rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)).
Definition term534 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 x1)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term755 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term747 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : Prop) (x1 : Prop) := imp ((x1 -> x0) /\ x1).
Definition term34 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((fun y0 : Prop => (((y0 -> x0) /\ (x1 -> x2)) /\ (y0 /\ x1)) -> (y0 /\ x0) /\ (x1 /\ x2)) x3).
Definition term699 (x0 : int) := or (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term301 (x0 : int) := fun y0 : int => (fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0.
Definition term545 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))).
Definition term97 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((((x0 -> x1) /\ (x2 -> x3)) /\ (x0 /\ x2)) -> (x0 /\ x1) /\ (x2 /\ x3)) -> (((x0 -> x1) /\ (x2 -> x3)) /\ (x0 /\ x2)) -> (x0 /\ x1) /\ (x2 /\ x3).
Definition term563 (x0 : int) := real_le (real_of_int (int_abs x0)).
Definition term519 (x0 : int) (x1 : int) := ~ ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))).
Definition term593 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term536 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))).
Definition term601 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term376 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term348 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term653 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term496 := real_of_num (NUMERAL (BIT1 0)).
Definition term743 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term776 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term529 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)).
Definition term292 (x0 : int) := or (exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))).
Definition term407 (x0 : int -> Prop) (x1 : int -> Prop) := (forall y0 : int, x0 y0) /\ (forall y0 : int, x1 y0).
Definition term659 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term402 (x0 : int) (x1 : int) := ~ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0))).
Definition term178 (x0 : int) (x1 : int) := ~ ((rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0))).
Definition term671 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term140 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term176 (x0 : int) (x1 : int) := (fun y0 : int => (rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))) x1.
Definition term474 (x0 : int) (x1 : int) := (~ ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))))) \/ (~ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1)))).
Definition term398 (x0 : int) (x1 : int) := (((int_mul x0 x1) = (int_mul x1 x0)) /\ (x1 = x1)) -> (rem (int_mul x0 x1) x1) = (rem (int_mul x1 x0) x1).
Definition term446 (x0 : int) := (fun y0 : int => (int_mul y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term299 (x0 : int) := exists y0 : int, ((fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0) \/ ((fun y1 : int => (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))))) y0).
Definition term281 := exists y0 : int, ((fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0) \/ ((fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (rem (int_mul y3 y4) y4) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))))) y0).
Definition term53 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ (x0 -> x1)) /\ x0) -> y0 /\ (x0 /\ x1)) x2.
Definition term752 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term751 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term72 (x0 : Prop) := ((True -> x0) /\ True) -> True /\ x0.
Definition term333 (x0 : int) := (~ (x0 = x0)) -> x0 = x0.
Definition term523 (x0 : int) (x1 : int) := int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term325 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term44 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((True -> x0) /\ (x2 -> x1)) /\ (True /\ x2).
Definition term364 (x0 : int) (x1 : int) := ((div (int_mul x0 x1) x1) = x0) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term259 := fun y0 : int => (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term454 := div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term345 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term187 := fun y0 : int => exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))).
Definition term603 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term11 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term424 := fun y0 : int => ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0) /\ ((fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) y0).
Definition term741 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term728 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term216 := exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (exists y1 : int, ~ ((div (int_mul y0 y1) y0) = y1)).
Definition term383 (x0 : int) (x1 : int) := (((div (int_mul x1 x0) x0) = (div (int_mul x0 x1) x0)) /\ ((div (int_mul x1 x0) x0) = x1)) -> (div (int_mul x0 x1) x0) = x1.
Definition term453 := div (int_of_num (NUMERAL 0)).
Definition term526 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term690 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))).
Definition term449 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term390 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((rem x0 x1) = (rem x2 x3))).
Definition term328 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((div x0 x1) = (div x2 x3))).
Definition term466 (x0 : int) (x1 : int) := (((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1)))) -> ((div (int_mul x0 x1) x1) = x0) /\ ((rem (int_mul x0 x1) x1) = (int_of_num (NUMERAL 0))).
Definition term758 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term705 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term770 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term495 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term439 (x0 : int) (x1 : int) := ((fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y0) y0) = x0) x1) /\ ((fun y0 : int => (rem (int_mul x0 y0) y0) = (int_of_num (NUMERAL 0))) x1).
Definition term321 (x0 : int) (x1 : int) := (fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul x0 y0) y0) = x0)) x1.
Definition term267 (x0 : int) := @eq Prop ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, ~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0))))).
Definition term266 (x0 : int) := @eq Prop ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, (fun y1 : int => ~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0)))) y0)).
Definition term255 := @eq Prop ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term254 := @eq Prop ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (exists y0 : int, (fun y1 : int => exists y2 : int, ~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0)))) y0)).
Definition term240 (x0 : int) := @eq Prop ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))).
Definition term239 (x0 : int) := @eq Prop ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1))) y0)).
Definition term228 := @eq Prop ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))).
Definition term227 := @eq Prop ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ (exists y0 : int, (fun y1 : int => exists y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2))) y0)).
Definition term380 (x0 : int) (x1 : int) (x2 : int) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term303 (x0 : int) := or (exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0).
Definition term285 := or (exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term591 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term183 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))) y0).
Definition term175 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))) y0).
Definition term163 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y1) = y2) y0).
Definition term156 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (~ (x0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) x0) = y1) y0).
Definition term90 (x0 : Prop) (x1 : Prop) := (x0 -> x1) /\ False.
Definition term200 (x0 : Prop) (x1 : int -> Prop) := x0 /\ (exists y0 : int, x1 y0).
Definition term430 (x0 : int) := fun y0 : int => (fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0.
Definition term433 (x0 : int) := fun y0 : int => (fun y1 : int => (rem (int_mul x0 y1) y1) = (int_of_num (NUMERAL 0))) y0.
Definition term10 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term19 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term317 := exists y0 : int, exists y1 : int, ((forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ ((forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term274 := exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term247 := exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))).
Definition term188 := exists y0 : int, exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))).
Definition term168 := exists y0 : int, exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)).
Definition term448 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term316 := fun y0 : int => exists y1 : int, ((forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ ((forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))).
Definition term246 := fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1))).
Definition term368 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term471 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term562 (x0 : int) := real_abs (real_of_int x0).
Definition term499 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term630 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term704 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term251 (x0 : int) := (fun y0 : int => exists y1 : int, ~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))) x0.
Definition term762 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term689 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term54 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ (x0 -> x1)) /\ x0) -> y0 /\ (x0 /\ x1)) True.
Definition term58 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ (x0 -> x1)) /\ x0) -> y0 /\ (x0 /\ x1)) False.
Definition term577 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term287 := fun y0 : int => (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (rem (int_mul y3 y4) y4) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))))) y0.
Definition term283 := fun y0 : int => (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0.
Definition term252 := fun y0 : int => (fun y1 : int => exists y2 : int, ~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0)))) y0.
Definition term225 := fun y0 : int => (fun y1 : int => exists y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2))) y0.
Definition term116 (x0 : int) := fun y0 : int => (int_mul x0 y0) = (int_mul y0 x0).
Definition term143 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term391 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((rem x0 x2) = (rem x1 x3)) \/ (~ (x2 = x3)).
Definition term335 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((div x0 x2) = (div x1 x3)) \/ (~ (x2 = x3)).
Definition term351 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term110 := (((~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> ((~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False) -> (~ (((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))))) -> (forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_mul y1 y0)) -> False.
Definition term204 (x0 : int) (x1 : int) := (fun y0 : int => ~ ((div (int_mul x0 y0) x0) = y0)) x1.
Definition term739 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term636 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term580 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term28 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term456 := @eq int (div (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term511 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term273 := fun y0 : int => exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term167 := fun y0 : int => exists y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)).
Definition term662 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term543 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term104 := ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) -> forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) -> forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0))).
Definition term337 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term91 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp (((False -> x0) /\ (x2 -> x1)) /\ (False /\ x2)).
Definition term586 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term702 (x0 : real) (x1 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1.
Definition term142 (x0 : int) := or (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term698 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term695 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0))))).
Definition term310 (x0 : int) (x1 : int) := or ((forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 x1) x0) = x1)))).
Definition term60 (x0 : Prop) (x1 : Prop) := True /\ (x0 -> x1).
Definition term542 (x0 : int) (x1 : int) := real_of_int (int_add (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term557 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term513 := real_add (real_of_num (NUMERAL 0)).
Definition term782 (x0 : int) (x1 : int) := (~ (~ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) /\ (((real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_int x1)) (real_of_num (NUMERAL 0)))))))) -> False.
Definition term277 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term359 (x0 : int) (x1 : int) := (((int_mul x0 x1) = (int_mul x1 x0)) /\ (x1 = x1)) -> (div (int_mul x0 x1) x1) = (div (int_mul x1 x0) x1).
Definition term51 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x0 /\ (x1 -> x2)) /\ x1) -> x0 /\ (x1 /\ x2).
Definition term531 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term626 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term576 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term434 (x0 : int) := forall y0 : int, (fun y1 : int => (rem (int_mul x0 y1) y1) = (int_of_num (NUMERAL 0))) y0.
Definition term431 (x0 : int) := forall y0 : int, (fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul x0 y1) y1) = x0) y0.
Definition term651 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term666 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term493 := int_of_num (NUMERAL (BIT1 0)).
Definition term530 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term520 (x0 : int) (x1 : int) := (int_le (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) \/ (int_le (int_add (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)).
Definition term763 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term680 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term415 := fun y0 : int => (fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) y0.
Definition term412 := fun y0 : int => (fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y2) = y1) y0.
Definition term497 := NUMERAL (BIT1 0).
Definition term244 (x0 : int) := fun y0 : int => (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0))).
Definition term206 (x0 : int) := and (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term406 (x0 : int) (x1 : int) := ((rem (int_mul x1 x0) x1) = (int_of_num (NUMERAL 0))) -> False.
Definition term242 (x0 : int) (x1 : int) := (forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y0 y1) y1) = y0)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 x1) x0) = x1))).
Definition term363 (x0 : Prop) := x0 -> ~ x0.
Definition term737 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term467 (x0 : int) (x1 : int) := ~ (~ ((~ (x1 = (int_of_num (NUMERAL 0)))) -> ((int_mul x0 x1) = (int_add (int_mul x0 x1) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs x1))))).
Definition term458 (x0 : int) (x1 : int) := rem (int_mul x0 x1).
Definition term589 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term186 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))) y0).
Definition term166 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y1 y2) y1) = y2) y0).
Definition term786 := ((forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1)) /\ ((forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term190 := (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y1) = (int_of_num (NUMERAL 0))) /\ (~ (forall y0 : int, forall y1 : int, (rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))).
Definition term171 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y1) = y0) /\ (~ (forall y0 : int, forall y1 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (div (int_mul y0 y1) y0) = y1)).
Definition term400 (x0 : int) (x1 : int) := ~ ((rem (int_mul x0 x1) x1) = (rem (int_mul x1 x0) x1)).
Definition term56 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ (x0 -> x1)) /\ x0) -> y0 /\ (x0 /\ x1)) x2).
Definition term221 (x0 : int) := @eq Prop ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (exists y0 : int, ~ ((div (int_mul x0 y0) x0) = y0))).
Definition term220 (x0 : int) := @eq Prop ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (exists y0 : int, (fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0)).
Definition term768 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term750 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term202 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (exists y0 : int, (fun y1 : int => ~ ((div (int_mul x0 y1) x0) = y1)) y0).
Definition term692 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term744 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term47 (x0 : Prop) (x1 : Prop) (x2 : Prop) := imp ((x0 /\ (x2 -> x1)) /\ x2).
Definition term308 (x0 : int) := @eq Prop ((exists y0 : int, (forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y1 y2) y2) = y1)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y0) x0) = y0)))) \/ (exists y0 : int, (forall y1 : int, forall y2 : int, (rem (int_mul y1 y2) y2) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y0) x0) = (int_of_num (NUMERAL 0)))))).
Definition term307 (x0 : int) := @eq Prop ((exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul x0 y1) x0) = y1)))) y0) \/ (exists y0 : int, (fun y1 : int => (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul x0 y1) x0) = (int_of_num (NUMERAL 0))))) y0)).
Definition term290 := @eq Prop ((exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y2 y3) y3) = y2)) /\ ((~ (y0 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y0 y1) y0) = y1)))) \/ (exists y0 : int, exists y1 : int, (forall y2 : int, forall y3 : int, (rem (int_mul y2 y3) y3) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y0 y1) y0) = (int_of_num (NUMERAL 0)))))).
Definition term289 := @eq Prop ((exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ ((div (int_mul y3 y4) y4) = y3)) /\ ((~ (y1 = (int_of_num (NUMERAL 0)))) /\ (~ ((div (int_mul y1 y2) y1) = y2)))) y0) \/ (exists y0 : int, (fun y1 : int => exists y2 : int, (forall y3 : int, forall y4 : int, (rem (int_mul y3 y4) y4) = (int_of_num (NUMERAL 0))) /\ (~ ((rem (int_mul y1 y2) y1) = (int_of_num (NUMERAL 0))))) y0)).
