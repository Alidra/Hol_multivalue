Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term829 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1))) /\ (int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) (int_abs (int_mul x1 x2))).
Definition term516 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)).
Definition term66 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term53 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term379 (x0 : int) := int_mul x0 (int_of_num (NUMERAL 0)).
Definition term319 (x0 : int) := fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))).
Definition term278 (x0 : int) := fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0)).
Definition term277 (x0 : int) := fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1)).
Definition term560 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) -> int_le x0 y0) x1.
Definition term131 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term630 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> (int_le (int_mul y1 x0) (int_mul y1 y0)) = (int_le x0 y0)) x1.
Definition term623 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_le x0 (int_sub y0 y1)) = (int_le (int_add x0 y1) y0)) x1.
Definition term592 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((int_lt x0 y0) /\ (int_le y0 y1)) -> int_lt x0 y1) x1.
Definition term284 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))) x1.
Definition term279 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) x1.
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((int_le x0 y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_mul x0 y1) (int_mul y0 y1)) x1.
Definition term404 (x0 : int) (x1 : int) := real_of_int (int_sub x0 (int_mul (div x0 x1) x1)).
Definition term167 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term544 (x0 : int) (x1 : int) (x2 : int) := real_ge (real_sub (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0))))).
Definition term452 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term773 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term32 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term674 (x0 : int) := real_le (real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term76 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term429 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_mul (real_of_int x1) (real_of_int (div x0 x1))).
Definition term340 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term499 (x0 : int) (x1 : int) (x2 : int) := real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))).
Definition term221 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = (int_add (int_mul x1 x3) x2)) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x3))).
Definition term552 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term88 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term230 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1)) x2.
Definition term217 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1)) x2.
Definition term207 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((int_le x0 y0) /\ (int_lt x1 y1)) -> int_lt (int_add x0 x1) (int_add y0 y1)) x2.
Definition term194 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((int_le x0 x1) /\ (int_lt y0 y1)) -> int_lt (int_add x0 y0) (int_add x1 y1)) x2.
Definition term321 := fun y0 : int => forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))).
Definition term252 := fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1)).
Definition term251 := fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2)).
Definition term450 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term338 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ ((int_of_num (NUMERAL 0)) = x0).
Definition term11 (x0 : int) (x1 : int) := ~ (~ ((int_add (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))) x0) = (int_mul x0 x1))).
Definition term575 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) (int_mul x2 (rem (div x1 x2) x0))) /\ (int_le (int_of_num (NUMERAL 0)) (rem x1 x2))) -> (int_le (int_of_num (NUMERAL 0)) (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))) = True.
Definition term236 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term34 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term795 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term35 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term50 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)).
Definition term683 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term443 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term430 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x0 x1)))).
Definition term140 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term311 (x0 : int) (x1 : int) := @eq Prop ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) /\ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1)))).
Definition term310 (x0 : int) (x1 : int) := @eq Prop ((forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0) /\ (forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y1)) = (int_add (int_mul x1 (rem (div x0 x1) y1)) (rem x0 x1))) y0)).
Definition term289 (x0 : int) := @eq Prop ((forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0)))).
Definition term288 (x0 : int) := @eq Prop ((forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem x0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div x0 y1) y2)) (rem x0 y1))) y0)).
Definition term267 := @eq Prop ((forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) /\ (forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1)))).
Definition term266 := @eq Prop ((forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (rem y1 (int_mul y2 y3)) = (int_add (int_mul y2 (rem (div y1 y2) y3)) (rem y1 y2))) y0)).
Definition term121 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term598 (x0 : int) (x1 : int) := exists y0 : int, (int_lt x0 y0) /\ (int_le y0 x1).
Definition term802 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term43 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term625 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le x0 (int_sub x1 y0)) = (int_le (int_add x0 y0) x1)) x2.
Definition term434 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int (div x1 x0))))) (real_of_int x1).
Definition term723 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term122 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term345 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term512 (x0 : int) (x1 : int) (x2 : int) := real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2).
Definition term747 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term75 (x0 : nat) := real_neg (real_of_num x0).
Definition term55 (x0 : int) (x1 : int) := or (int_le (int_add (int_add (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))) x0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1)).
Definition term610 (x0 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0.
Definition term232 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term675 := real_of_int (int_of_num (NUMERAL 0)).
Definition term391 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1)))).
Definition term69 (x0 : Prop) := ~ (~ x0).
Definition term113 := real_of_num (NUMERAL 0).
Definition term573 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term526 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2))))).
Definition term737 := real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term449 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term390 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1))).
Definition term520 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int (div (div x1 x2) x0)))) (real_of_int (div x1 x2)).
Definition term385 (x0 : int) (x1 : int) := True /\ (x0 = (int_add (int_mul x1 (div x0 x1)) (rem x0 x1))).
Definition term317 (x0 : int) (x1 : int) := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1))).
Definition term652 (x0 : int) (x1 : int) := (int_le x0 (int_abs x0)) /\ (int_le (int_of_num (NUMERAL 0)) (int_abs x1)).
Definition term102 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term533 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x1) (real_mul (real_of_int (div (div x0 x1) x2)) (real_of_int x2)).
Definition term240 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ (~ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term302 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) x2) = (div x0 (int_mul x1 x2)).
Definition term830 (x0 : int) (x1 : int) (x2 : int) := (x0 = (int_add (int_mul (div (div x0 x1) x2) (int_mul x1 x2)) (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1))) /\ (int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) (int_abs (int_mul x1 x2)))).
Definition term473 (x0 : int) (x1 : int) (x2 : int) := real_le (real_of_int (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))))).
Definition term673 (x0 : int) := int_le (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term235 := int_of_num (NUMERAL 0).
Definition term596 (x0 : int) (x1 : int) (x2 : int) := (int_lt x0 x1) /\ (int_le x1 x2).
Definition term531 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x0) (real_of_int (div (div x2 x1) x0))))) (real_add (real_mul (real_of_int x1) (real_of_int (div x2 x1))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x2 x1)))) (real_of_int x2))).
Definition term676 (x0 : int) := real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term14 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term690 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0)).
Definition term200 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y1) /\ (int_lt y2 y3)) -> int_lt (int_add y0 y2) (int_add y1 y3)) -> int_lt (int_add x0 x1) (int_add x2 x3).
Definition term229 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2)) x1.
Definition term215 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2)) x1.
Definition term206 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((int_le x0 y1) /\ (int_lt y0 y2)) -> int_lt (int_add x0 y0) (int_add y1 y2)) x1.
Definition term192 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((int_le x0 y0) /\ (int_lt y1 y2)) -> int_lt (int_add x0 y1) (int_add y0 y2)) x1.
Definition term30 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term649 (x0 : int) (x1 : int) := int_le (int_mul x0 (int_abs x1)) (int_mul (int_abs x0) (int_abs x1)).
Definition term68 (x0 : int) (x1 : int) := (real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int x0))) \/ (real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1))).
Definition term299 (x0 : int) (x1 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0)).
Definition term401 (x0 : int) (x1 : int) := real_mul (real_of_int x1) (real_of_int (div x0 x1)).
Definition term801 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term721 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term120 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term582 (x0 : int) (x1 : int) (x2 : int) := (~ (x2 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (rem (div x0 x1) x2)) = True.
Definition term581 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) = True.
Definition term804 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term729 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term124 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term155 (x0 : int) (x1 : int) := real_sub (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)).
Definition term681 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term545 (x0 : int) (x1 : int) (x2 : int) := real_ge (real_sub (real_of_int x1) (real_add (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term453 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term497 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))).
Definition term490 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_mul (div (div x0 x1) x2) x2).
Definition term101 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term8 (x0 : int) (x1 : int) (x2 : int) := int_le (int_mul x0 x2) (int_mul x1 x2).
Definition term632 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_le (int_mul y0 x0) (int_mul y0 x1)) = (int_le x0 x1)) x2.
Definition term611 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0) x1.
Definition term816 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term163 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term375 (x0 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x0)) -> (int_lt (int_of_num (NUMERAL 0)) x0) = False.
Definition term364 (x0 : int) := (~ ((int_of_num (NUMERAL 0)) = x0)) -> ((int_of_num (NUMERAL 0)) = x0) = False.
Definition term738 := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term414 (x0 : int) (x1 : int) := int_le (int_add (int_add (int_mul x0 (div x1 x0)) (int_sub x1 (int_mul (div x1 x0) x0))) (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term547 (x0 : int) (x1 : int) (x2 : int) := real_ge (real_sub (real_of_int x1) (real_add (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term615 (x0 : int) (x1 : int) (x2 : int) := and (int_le (int_mul x1 (rem (div x0 x1) x2)) (int_mul x1 (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0)))))).
Definition term619 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1) = (int_lt y0 y1)) x0.
Definition term609 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1) x0.
Definition term604 (x0 : int) := (fun y0 : int => forall y1 : int, (exists y2 : int, (int_lt y0 y2) /\ (int_le y2 y1)) -> int_lt y0 y1) x0.
Definition term568 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_of_num (NUMERAL 0)) (int_add y0 y1)) x0.
Definition term562 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_of_num (NUMERAL 0)) (int_mul y0 y1)) x0.
Definition term558 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) -> int_le y0 y1) x0.
Definition term551 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) x0.
Definition term323 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = ((int_lt y0 y1) \/ (y0 = y1))) x0.
Definition term208 (x0 : int) := (fun y0 : int => forall y1 : int, (rem y0 y1) = (int_sub y0 (int_mul (div y0 y1) y1))) x0.
Definition term175 (x0 : int) := (fun y0 : int => forall y1 : int, (int_abs (int_mul y0 y1)) = (int_mul (int_abs y0) (int_abs y1))) x0.
Definition term318 (x0 : int) (x1 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1))).
Definition term685 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term703 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1) x2.
Definition term377 (x0 : int) (x1 : int) (x2 : int) := False -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term439 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term82 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term821 := S (Nat.add (BIT1 0) 0).
Definition term631 (x0 : int) (x1 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_le (int_mul y0 x0) (int_mul y0 x1)) = (int_le x0 x1).
Definition term290 (x0 : int) (x1 : int) := and ((fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) x1).
Definition term525 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))).
Definition term70 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int x0))) \/ (real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1))))).
Definition term748 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term743 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))).
Definition term405 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int (int_mul (div x0 x1) x1)).
Definition term682 (x0 : int) := real_sub (real_of_int x0) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term628 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y2) -> (int_le (int_mul y2 y0) (int_mul y2 y1)) = (int_le y0 y1)) x0.
Definition term621 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_le y0 (int_sub y1 y2)) = (int_le (int_add y0 y2) y1)) x0.
Definition term590 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((int_lt y0 y1) /\ (int_le y1 y2)) -> int_lt y0 y2) x0.
Definition term260 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))) x0.
Definition term253 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) x0.
Definition term228 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3)) x0.
Definition term213 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) x0.
Definition term205 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y2) /\ (int_lt y1 y3)) -> int_lt (int_add y0 y1) (int_add y2 y3)) x0.
Definition term190 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y1) /\ (int_lt y2 y3)) -> int_lt (int_add y0 y2) (int_add y1 y3)) x0.
Definition term1 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le (int_of_num (NUMERAL 0)) y2)) -> int_le (int_mul y0 y2) (int_mul y1 y2)) x0.
Definition term358 (x0 : int) (x1 : int) (x2 : int) := int_mul x1 (rem (div x0 x1) x2).
Definition term654 (x0 : int) (x1 : int) := (~ (int_le x0 (int_abs x0))) \/ (~ (int_le (int_of_num (NUMERAL 0)) (int_abs x1))).
Definition term428 (x0 : int) (x1 : int) := real_of_int (div x0 x1).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := ((int_le x0 x1) /\ (int_le (int_of_num (NUMERAL 0)) x2)) -> int_le (int_mul x0 x2) (int_mul x1 x2).
Definition term393 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term374 (x0 : int) (x1 : int) (x2 : int) := ((div (div x1 x2) x0) = (div x1 (int_mul x2 x0))) /\ ((rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))).
Definition term752 (x0 : int) := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term759 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term606 (x0 : int) (x1 : int) (x2 : int) := (exists y0 : int, (int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) y0) /\ (int_le y0 (int_abs (int_mul x1 x2)))) -> int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) (int_abs (int_mul x1 x2)).
Definition term339 := int_lt (int_of_num (NUMERAL 0)).
Definition term823 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_abs (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) -> False) -> ~ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_abs (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term335 (x0 : int) := (fun y0 : int => (int_mul (int_of_num (NUMERAL 0)) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term329 (x0 : int) := (fun y0 : int => (div (int_of_num (NUMERAL 0)) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term491 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int (div (div x0 x1) x2)) (real_of_int x2).
Definition term182 (x0 : int) := fun y0 : int => (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0) = (int_lt x0 y0).
Definition term511 (x0 : int) (x1 : int) (x2 : int) := real_le (real_add (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term423 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term269 (x0 : int) := and (forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))).
Definition term259 := and (forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))).
Definition term482 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int (div (div x0 x1) x2)) (real_mul (real_of_int x1) (real_of_int x2))).
Definition term99 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term702 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x1))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term36 (x0 : int) := real_of_int (int_sub x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term325 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = ((int_lt x0 y0) \/ (x0 = y0))) x1.
Definition term687 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term688 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term448 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term715 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term466 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul (div (div x0 x1) x2) (int_mul x1 x2)).
Definition term168 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term600 (x0 : int) (x1 : int) := (exists y0 : int, (int_lt x0 y0) /\ (int_le y0 x1)) -> int_lt x0 x1.
Definition term174 (x0 : int) (x1 : int) := ~ ((real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int x0))) \/ (real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)))).
Definition term799 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term797 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term719 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term717 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term118 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term112 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term686 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))).
Definition term496 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x0 x1)) (real_mul (real_of_int (div (div x0 x1) x2)) (real_of_int x2)))).
Definition term445 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term569 (x0 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (int_add x0 y0).
Definition term563 (x0 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (int_mul x0 y0).
Definition term218 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0).
Definition term195 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((int_le x0 x2) /\ (int_lt x1 y0)) -> int_lt (int_add x0 x1) (int_add x2 y0).
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, ((int_le x0 x1) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_mul x0 y0) (int_mul x1 y0).
Definition term559 (x0 : int) := forall y0 : int, (int_lt x0 y0) -> int_le x0 y0.
Definition term381 (x0 : int) (x1 : int) := rem (div x0 x1) (int_of_num (NUMERAL 0)).
Definition term58 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul x1 x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1)).
Definition term557 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term297 (x0 : int) (x1 : int) := (forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0) /\ (forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y1)) = (int_add (int_mul x1 (rem (div x0 x1) y1)) (rem x0 x1))) y0).
Definition term275 (x0 : int) := (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem x0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div x0 y1) y2)) (rem x0 y1))) y0).
Definition term249 := (forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0) /\ (forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (rem y1 (int_mul y2 y3)) = (int_add (int_mul y2 (rem (div y1 y2) y3)) (rem y1 y2))) y0).
Definition term130 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term633 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (int_mul x0 x1) (int_mul x0 x2)) = (int_le x1 x2).
Definition term419 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1)))).
Definition term57 (x0 : int) (x1 : int) := int_le (int_add (int_mul x1 x0) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1).
Definition term824 (x0 : int) (x1 : int) := ~ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_abs (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term474 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))).
Definition term667 (x0 : int) := real_add (real_abs (real_of_int x0)).
Definition term293 (x0 : int) (x1 : int) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) /\ (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1))).
Definition term146 (x0 : int) (x1 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term826 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, (int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) y0) /\ (int_le y0 (int_abs (int_mul x1 x2))).
Definition term668 (x0 : int) := real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term784 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term778 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term343 := @eq int (int_of_num (NUMERAL 0)).
Definition term494 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x1) (real_sub (real_of_int (div x0 x1)) (real_mul (real_of_int (div (div x0 x1) x2)) (real_of_int x2))).
Definition term138 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term244 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term348 (x0 : int) (x1 : int) (x2 : int) := div (div x0 x1) x2.
Definition term616 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_mul x2 (rem (div x1 x2) x0)) (int_mul x2 (int_sub (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))))) /\ (int_lt (rem x1 x2) x2).
Definition term637 (x0 : int) (x1 : int) (x2 : int) := int_le (rem (div x0 x1) x2) (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0)))).
Definition term489 (x0 : int) (x1 : int) (x2 : int) := int_mul (div (div x0 x1) x2) x2.
Definition term627 (x0 : int) (x1 : int) (x2 : int) := int_le (int_add x0 x1) x2.
Definition term510 (x0 : int) (x1 : int) (x2 : int) := real_le (real_of_int (int_add (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))) (int_of_num (NUMERAL (BIT1 0))))).
Definition term422 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1))) (int_of_num (NUMERAL (BIT1 0))))).
Definition term528 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x2) (real_mul (real_of_int x0) (real_of_int (div (div x1 x2) x0))))) (real_mul (real_of_int x2) (real_of_int (div x1 x2))).
Definition term424 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1).
Definition term761 (x0 : int) := real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term756 (x0 : int) := real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))).
Definition term384 (x0 : int) (x1 : int) := int_add (int_mul x1 (div x0 x1)) (rem x0 x1).
Definition term285 (x0 : int) (x1 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1)).
Definition term280 (x0 : int) (x1 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0)).
Definition term808 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term92 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term657 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term669 (x0 : int) := real_le (real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))).
Definition term680 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_abs (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term570 (x0 : int) (x1 : int) := (fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (int_add x0 y0)) x1.
Definition term564 (x0 : int) (x1 : int) := (fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (int_mul x0 y0)) x1.
Definition term810 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term78 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term608 (x0 : int) (x1 : int) := int_mul x0 (int_sub (int_abs x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term537 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int (div (div x2 x0) x1)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int (div (div x2 x0) x1)))))) (real_of_int x2).
Definition term369 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x2) -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term37 (x0 : int) := real_sub (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term60 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term49 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1)).
Definition term336 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) x0.
Definition term815 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term160 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term605 (x0 : int) (x1 : int) := (fun y0 : int => (exists y1 : int, (int_lt x0 y1) /\ (int_le y1 y0)) -> int_lt x0 y0) x1.
Definition term415 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_mul x0 (div x1 x0)) (int_sub x1 (int_mul (div x1 x0) x0))) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term493 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_of_int (div x0 x1)) (real_mul (real_of_int (div (div x0 x1) x2)) (real_of_int x2)).
Definition term595 (x0 : int) (x1 : int) (x2 : int) := ((int_lt x1 x0) /\ (int_le x0 x2)) -> int_lt x1 x2.
Definition term446 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term436 (x0 : int) (x1 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x0 x1))).
Definition term327 (x0 : int) := (fun y0 : int => (int_add (int_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term116 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term506 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term418 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1)))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term231 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term543 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))).
Definition term587 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) (int_mul x2 (rem (div x1 x2) x0))) /\ (int_le (int_of_num (NUMERAL 0)) (rem x1 x2)).
Definition term507 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))))).
Definition term104 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_int x1).
Definition term394 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term550 (x0 : int) (x1 : int) (x2 : int) := ~ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1)))))) \/ (real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))).
Definition term162 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term416 (x0 : int) (x1 : int) := int_add (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1))) (int_of_num (NUMERAL (BIT1 0))).
Definition term134 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_of_int x1)).
Definition term502 (x0 : int) (x1 : int) (x2 : int) := int_le (int_add (int_add (int_mul (div (div x2 x1) x0) (int_mul x1 x0)) (int_add (int_mul x1 (int_sub (div x2 x1) (int_mul (div (div x2 x1) x0) x0))) (int_sub x2 (int_mul (div x2 x1) x1)))) (int_of_num (NUMERAL (BIT1 0)))) x2.
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term812 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term692 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term664 (x0 : int) := real_of_int (int_abs x0).
Definition term819 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term166 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term442 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term514 (x0 : int) (x1 : int) (x2 : int) := ~ (~ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1)))))) \/ (real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))).
Definition term426 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0))))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term141 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term614 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_lt (rem x0 x1) x1) = True.
Definition term467 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term800 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term720 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term119 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : int) (x1 : int) := real_of_int (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term730 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term716 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term111 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term757 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term135 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x1) (real_of_int x0)) (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term62 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 x1)).
Definition term176 (x0 : int) := forall y0 : int, (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0)).
Definition term740 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_int x0)).
Definition term554 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term328 (x0 : int) := int_add (int_of_num (NUMERAL 0)) x0.
Definition term727 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term103 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term173 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int x0))) \/ (real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)))))) -> False) -> ~ ((real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int x0))) \/ (real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)))).
Definition term161 := real_le (real_of_num (NUMERAL 0)).
Definition term578 (x0 : int) (x1 : int) := (int_lt x0 x1) -> (int_le x0 x1) = True.
Definition term199 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := int_lt (int_add x0 x1) (int_add x2 x3).
Definition term21 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term312 (x0 : int) (x1 : int) (x2 : int) := and ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) x2).
Definition term169 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term566 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1).
Definition term617 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_mul x1 (rem (div x0 x1) x2)) (int_mul x1 (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0)))))) /\ True.
Definition term645 (x0 : int) (x1 : int) := int_mul x0 (int_abs x1).
Definition term766 (x0 : int) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term492 (x0 : int) (x1 : int) := real_sub (real_of_int (div x0 x1)).
Definition term809 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term271 (x0 : int) := (forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) /\ (forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))).
Definition term265 := (forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) /\ (forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))).
Definition term527 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2))))).
Definition term782 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term488 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_of_int (div x0 x1)) (real_of_int (int_mul (div (div x0 x1) x2) x2)).
Definition term684 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term268 (x0 : int) := and ((fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) x0).
Definition term771 := real_lt (real_of_num (NUMERAL 0)).
Definition term612 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> int_lt (rem x0 x1) x1.
Definition term699 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term437 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_int x1) (real_of_int (div x0 x1))).
Definition term468 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))).
Definition term305 (x0 : int) (x1 : int) := and (forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0).
Definition term283 (x0 : int) := and (forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0).
Definition term258 := and (forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0).
Definition term96 (x0 : int) := real_add (real_of_int x0).
Definition term476 (x0 : int) (x1 : int) (x2 : int) := int_mul (div (div x0 x1) x2) (int_mul x1 x2).
Definition term767 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term658 (x0 : int) := ~ (int_le x0 (int_abs x0)).
Definition term23 (x0 : int) (x1 : int) := real_of_int (int_add (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term148 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))).
Definition term791 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term693 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term662 (x0 : int) := real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term532 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int (div (div x2 x0) x1))))) (real_of_int x2).
Definition term171 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term597 (x0 : int) (x1 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_lt y0 y1) /\ (int_le y1 y2)) -> int_lt y0 y2) -> int_lt x0 x1.
Definition term398 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1))).
Definition term803 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term712 (x0 : int) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term107 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term480 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int (div (div x0 x1) x2)) (real_mul (real_of_int x1) (real_of_int x2)).
Definition term38 (x0 : nat) := real_of_int (int_of_num x0).
Definition term179 (x0 : int) (x1 : int) := int_mul (int_abs x0) (int_abs x1).
Definition term642 (x0 : int) (x1 : int) (x2 : int) := (~ (x2 = (int_of_num (NUMERAL 0)))) -> (int_lt (rem (div x0 x1) x2) (int_abs x2)) = True.
Definition term641 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (int_lt (rem x0 x1) (int_abs x1)) = True.
Definition term827 (x0 : int) (x1 : int) (x2 : int) := fun y0 : int => (int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) y0) /\ (int_le y0 (int_abs (int_mul x1 x2))).
Definition term588 (x0 : int) (x1 : int) (x2 : int) := int_le (int_of_num (NUMERAL 0)) (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term620 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0) = (int_lt x0 y0)) x1.
Definition term127 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term825 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) (int_add (int_mul x1 (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0))))) x1)) /\ (int_le (int_add (int_mul x1 (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0))))) x1) (int_abs (int_mul x1 x2))).
Definition term239 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term760 (x0 : int) := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term123 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term504 (x0 : int) (x1 : int) (x2 : int) := int_add (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))) (int_of_num (NUMERAL (BIT1 0))).
Definition term89 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term389 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 (div x1 x0)) (int_sub x1 (int_mul (div x1 x0) x0)))) \/ (int_le (int_add (int_add (int_mul x0 (div x1 x0)) (int_sub x1 (int_mul (div x1 x0) x0))) (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term180 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term704 (x0 : real) (x1 : real) (x2 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_ge (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term26 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1).
Definition term407 (x0 : int) (x1 : int) := real_of_int (int_mul (div x0 x1) x1).
Definition term22 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term555 (x0 : int) (x1 : int) := (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term109 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term523 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int (div (div x1 x2) x0))))) (real_mul (real_of_int x2) (real_of_int (div x1 x2))).
Definition term477 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_mul (div (div x0 x1) x2) (int_mul x1 x2)).
Definition term366 (x0 : int) := imp (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term361 := int_add (int_of_num (NUMERAL 0)).
Definition term636 (x0 : int) := int_sub (int_abs x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term607 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_mul x2 (rem (div x0 x2) x1)) (int_mul x2 (int_sub (int_abs x1) (int_of_num (NUMERAL (BIT1 0)))))) /\ (int_lt (rem x0 x2) x2)) -> int_lt (int_add (int_mul x2 (rem (div x0 x2) x1)) (rem x0 x2)) (int_add (int_mul x2 (int_sub (int_abs x1) (int_of_num (NUMERAL (BIT1 0))))) x2).
Definition term820 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term170 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term93 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term349 (x0 : int) (x1 : int) (x2 : int) := @eq int (div (div x0 x1) x2).
Definition term561 (x0 : int) (x1 : int) := (int_lt x0 x1) -> int_le x0 x1.
Definition term144 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term529 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x2) (real_mul (real_of_int x0) (real_of_int (div (div x1 x2) x0))))) (real_mul (real_of_int x2) (real_of_int (div x1 x2)))).
Definition term115 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term762 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term744 (x0 : int) := real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term459 (x0 : int) (x1 : int) (x2 : int) := and ((div x0 (int_mul x1 x2)) = (div (div x0 x1) x2)).
Definition term677 (x0 : int) := or (~ (int_le x0 (int_abs x0))).
Definition term137 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term735 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term594 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((int_lt x1 x0) /\ (int_le x0 y0)) -> int_lt x1 y0) x2.
Definition term372 (x0 : int) (x1 : int) (x2 : int) := and ((div (div x0 x1) x2) = (div x0 (int_mul x1 x2))).
Definition term708 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term147 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term183 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term618 (x0 : int) (x1 : int) (x2 : int) := int_le (int_mul x1 (rem (div x0 x1) x2)) (int_mul x1 (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0))))).
Definition term106 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term655 (x0 : int) := int_le x0 (int_abs x0).
Definition term541 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))))).
Definition term663 (x0 : int) := real_add (real_of_int (int_abs x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term553 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))) x1.
Definition term298 (x0 : int) (x1 : int) := forall y0 : int, ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0) /\ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y1)) = (int_add (int_mul x1 (rem (div x0 x1) y1)) (rem x0 x1))) y0).
Definition term276 (x0 : int) := forall y0 : int, ((fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0) /\ ((fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem x0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div x0 y1) y2)) (rem x0 y1))) y0).
Definition term250 := forall y0 : int, ((fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0) /\ ((fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (rem y1 (int_mul y2 y3)) = (int_add (int_mul y2 (rem (div y1 y2) y3)) (rem y1 y2))) y0).
Definition term363 (x0 : int) := ~ ((int_of_num (NUMERAL 0)) = x0).
Definition term355 := rem (int_of_num (NUMERAL 0)).
Definition term178 (x0 : int) (x1 : int) := int_abs (int_mul x0 x1).
Definition term798 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term768 (x0 : int) := or ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term646 (x0 : int) (x1 : int) := int_le (int_add (int_mul x1 (int_sub (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))) x1).
Definition term451 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term397 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 (x0 : int) := real_mul (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term749 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term745 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term156 (x0 : int) (x1 : int) := real_sub (real_add (real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term90 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term386 (x0 : int) (x1 : int) := int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1)).
Definition term433 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int (div x1 x0)))) (real_of_int x1)).
Definition term54 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term515 (x0 : int) (x1 : int) (x2 : int) := real_ge (real_sub (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term427 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term154 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term71 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_of_int x1) (real_of_int x0)) (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term524 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))).
Definition term371 (x0 : int) (x1 : int) (x2 : int) := True -> (div (div x0 x1) x2) = (div x0 (int_mul x1 x2)).
Definition term460 (x0 : int) (x1 : int) (x2 : int) := ((div x1 (int_mul x2 x0)) = (div (div x1 x2) x0)) /\ ((rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))).
Definition term46 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term402 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x1 (div x0 x1))).
Definition term789 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term779 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term732 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term198 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_le x0 x1) /\ (int_lt x2 x3).
Definition term671 (x0 : int) := real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term678 (x0 : int) := or (real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((int_le x0 x1) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_mul x0 y0) (int_mul x1 y0)) x2.
Definition term296 (x0 : int) := forall y0 : int, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) /\ (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))).
Definition term274 := forall y0 : int, (forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) /\ (forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))).
Definition term243 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term18 (x0 : int) (x1 : int) := int_le (int_add (int_add (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))) x0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 x1).
Definition term487 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2)).
Definition term94 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term209 (x0 : int) := forall y0 : int, (rem x0 y0) = (int_sub x0 (int_mul (div x0 y0) y0)).
Definition term469 (x0 : int) (x1 : int) (x2 : int) := ~ (~ (x1 = (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))))).
Definition term360 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x1 (rem (div x0 x1) x2)).
Definition term97 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term273 := fun y0 : int => (forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) /\ (forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))).
Definition term629 (x0 : int) := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> (int_le (int_mul y1 x0) (int_mul y1 y0)) = (int_le x0 y0).
Definition term622 (x0 : int) := forall y0 : int, forall y1 : int, (int_le x0 (int_sub y0 y1)) = (int_le (int_add x0 y1) y0).
Definition term602 := forall y0 : int, forall y1 : int, (exists y2 : int, (int_lt y0 y2) /\ (int_le y2 y1)) -> int_lt y0 y1.
Definition term591 (x0 : int) := forall y0 : int, forall y1 : int, ((int_lt x0 y0) /\ (int_le y0 y1)) -> int_lt x0 y1.
Definition term589 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_lt y0 y1) /\ (int_le y1 y2)) -> int_lt y0 y2.
Definition term322 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) /\ ((int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))).
Definition term320 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))).
Definition term264 := forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1)).
Definition term261 (x0 : int) := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0)).
Definition term257 := forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2)).
Definition term254 (x0 : int) := forall y0 : int, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1)).
Definition term226 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term225 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2).
Definition term224 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1).
Definition term216 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1).
Definition term214 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2).
Definition term212 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3).
Definition term203 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y2) /\ (int_lt y1 y3)) -> int_lt (int_add y0 y1) (int_add y2 y3).
Definition term202 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le x0 y1) /\ (int_lt y0 y2)) -> int_lt (int_add x0 y0) (int_add y1 y2).
Definition term201 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((int_le x0 y0) /\ (int_lt x1 y1)) -> int_lt (int_add x0 x1) (int_add y0 y1).
Definition term193 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((int_le x0 x1) /\ (int_lt y0 y1)) -> int_lt (int_add x0 y0) (int_add x1 y1).
Definition term191 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le x0 y0) /\ (int_lt y1 y2)) -> int_lt (int_add x0 y1) (int_add y0 y2).
Definition term189 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y1) /\ (int_lt y2 y3)) -> int_lt (int_add y0 y2) (int_add y1 y3).
Definition term188 := forall y0 : int, forall y1 : int, (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1) = (int_lt y0 y1).
Definition term187 := forall y0 : int, forall y1 : int, (int_lt y0 y1) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1).
Definition term2 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le x0 y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_mul x0 y1) (int_mul y0 y1).
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le (int_of_num (NUMERAL 0)) y2)) -> int_le (int_mul y0 y2) (int_mul y1 y2).
Definition term181 (x0 : int) := fun y0 : int => (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term86 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term813 := real_ge (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term152 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term478 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int (div (div x0 x1) x2)) (real_of_int (int_mul x1 x2)).
Definition term359 (x0 : int) := int_mul (int_of_num (NUMERAL 0)) (rem (int_of_num (NUMERAL 0)) x0).
Definition term61 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term691 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term455 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term734 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term775 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term818 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term165 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term233 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term392 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term733 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term45 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term316 (x0 : int) (x1 : int) := fun y0 : int => ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0) /\ ((fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y1)) = (int_add (int_mul x1 (rem (div x0 x1) y1)) (rem x0 x1))) y0).
Definition term117 := S (Nat.add 0 0).
Definition term7 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x1) /\ (int_le (int_of_num (NUMERAL 0)) x2).
Definition term805 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term79 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term577 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le (int_of_num (NUMERAL 0)) (rem (div x0 x1) x2))) -> (int_le (int_of_num (NUMERAL 0)) (int_mul x1 (rem (div x0 x1) x2))) = True.
Definition term486 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x1) (real_of_int (int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2))).
Definition term142 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term77 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term292 (x0 : int) (x1 : int) := ((fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) x1) /\ ((fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))) x1).
Definition term613 (x0 : int) (x1 : int) := int_lt (rem x0 x1) x1.
Definition term718 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term807 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term81 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term48 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term411 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))).
Definition term672 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (int_abs x0)).
Definition term19 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))) x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_mul x0 x1)).
Definition term295 (x0 : int) := fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (div (div x0 y0) y1) = (div x0 (int_mul y0 y1))) /\ (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (rem x0 (int_mul y0 y1)) = (int_add (int_mul y0 (rem (div x0 y0) y1)) (rem x0 y0))).
Definition term334 (x0 : int) := div x0 (int_of_num (NUMERAL 0)).
Definition term584 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le (int_of_num (NUMERAL 0)) (rem (div x0 x1) x2)).
Definition term763 (x0 : int) := real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term758 (x0 : int) := real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term159 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term513 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1)))))) \/ (real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)).
Definition term51 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term634 (x0 : int) (x1 : int) (x2 : int) := int_le (int_mul x1 x0) (int_mul x1 x2).
Definition term186 := fun y0 : int => forall y1 : int, (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1) = (int_lt y0 y1).
Definition term185 := fun y0 : int => forall y1 : int, (int_lt y0 y1) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1).
Definition term579 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x0) = True.
Definition term400 (x0 : int) (x1 : int) := real_of_int (int_mul x1 (div x0 x1)).
Definition term753 (x0 : int) := (real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term705 (x0 : int) := (real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term698 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term635 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (int_mul x1 (rem (div x0 x1) x2)) (int_mul x1 (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0)))))) = (int_le (rem (div x0 x1) x2) (int_sub (int_abs x2) (int_of_num (NUMERAL (BIT1 0))))).
Definition term157 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term151 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_of_int x1) (real_of_int x0)) (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term659 (x0 : int) := int_le (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term565 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> int_le (int_of_num (NUMERAL 0)) (int_mul x0 x1).
Definition term136 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_of_int x1)) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term341 (x0 : int) := or (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term660 (x0 : int) := real_le (real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term522 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x2) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int (div (div x1 x2) x0)))) (real_of_int (div x1 x2))).
Definition term441 (x0 : int) (x1 : int) := real_sub (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term387 (x0 : int) (x1 : int) := ~ (~ (x0 = (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1))))).
Definition term517 (x0 : int) (x1 : int) (x2 : int) := real_of_int (div (div x0 x1) x2).
Definition term351 (x0 : int) (x1 : int) (x2 : int) := div x0 (int_mul x1 x2).
Definition term125 := real_mul (real_of_num (NUMERAL 0)).
Definition term714 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term346 (x0 : int) (x1 : int) := div (div x0 x1).
Definition term24 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term728 := NUMERAL (BIT0 (BIT1 0)).
Definition term287 (x0 : int) := forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem x0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div x0 y1) y2)) (rem x0 y1))) y0.
Definition term282 (x0 : int) := forall y0 : int, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0.
Definition term263 := forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (rem y1 (int_mul y2 y3)) = (int_add (int_mul y2 (rem (div y1 y2) y3)) (rem y1 y2))) y0.
Definition term256 := forall y0 : int, (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0.
Definition term694 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term367 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) x2) = (div x0 (int_mul x1 x2)).
Definition term237 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term519 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (div x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))).
Definition term603 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_lt y0 y1) /\ (int_le y1 y2)) -> int_lt y0 y2) -> forall y0 : int, forall y1 : int, (exists y2 : int, (int_lt y0 y2) /\ (int_le y2 y1)) -> int_lt y0 y1.
Definition term227 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term204 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y1) /\ (int_lt y2 y3)) -> int_lt (int_add y0 y2) (int_add y1 y3)) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((int_le y0 y2) /\ (int_lt y1 y3)) -> int_lt (int_add y0 y1) (int_add y2 y3).
Definition term10 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le (int_of_num (NUMERAL 0)) y2)) -> int_le (int_mul y0 y2) (int_mul y1 y2)) -> forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le (int_of_num (NUMERAL 0)) y2)) -> int_le (int_mul y0 y2) (int_mul y1 y2).
Definition term751 := and (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term133 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term396 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term666 (x0 : int) := real_add (real_of_int (int_abs x0)).
Definition term542 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))).
Definition term470 (x0 : int) (x1 : int) (x2 : int) := ~ (x1 = (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))))).
Definition term28 (x0 : int) (x1 : int) := int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0)))).
Definition term306 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1))) x2.
Definition term301 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) x2.
Definition term42 (x0 : int) := real_sub (real_of_int x0).
Definition term84 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term354 (x0 : int) (x1 : int) := rem (div x0 x1).
Definition term440 (x0 : int) (x1 : int) := real_sub (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))).
Definition term56 (x0 : int) (x1 : int) := or (real_le (real_add (real_add (real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term219 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0)) x3.
Definition term376 (x0 : int) (x1 : int) (x2 : int) := False -> (div (div x0 x1) x2) = (div x0 (int_mul x1 x2)).
Definition term196 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((int_le x0 x2) /\ (int_lt x1 y0)) -> int_lt (int_add x0 x1) (int_add x2 y0)) x3.
Definition term129 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term406 (x0 : int) (x1 : int) := int_mul (div x0 x1) x1.
Definition term495 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_mul x1 (int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2)))).
Definition term13 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term74 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term546 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_of_int x1) (real_add (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term410 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1))).
Definition term362 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2).
Definition term326 (x0 : int) (x1 : int) := (int_lt x0 x1) \/ (x0 = x1).
Definition term484 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0)))) (real_of_int (int_sub x1 (int_mul (div x1 x2) x2))).
Definition term479 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int (div (div x0 x1) x2)).
Definition term248 (x0 : int -> Prop) (x1 : int -> Prop) := forall y0 : int, (x0 y0) /\ (x1 y0).
Definition term145 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term33 (x0 : int) := int_sub x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term790 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term785 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term780 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term370 (x0 : int) (x1 : int) (x2 : int) := ((int_lt (int_of_num (NUMERAL 0)) x2) -> (div (div x1 x2) x0) = (div x1 (int_mul x2 x0))) /\ ((int_lt (int_of_num (NUMERAL 0)) x2) -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))).
Definition term315 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) x2) -> (div (div x1 x2) x0) = (div x1 (int_mul x2 x0))) /\ ((int_le (int_of_num (NUMERAL 0)) x2) -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))).
Definition term580 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term638 (x0 : int) (x1 : int) (x2 : int) := int_le (int_add (rem (div x0 x1) x2) (int_of_num (NUMERAL (BIT1 0)))) (int_abs x2).
Definition term725 := Nat.add (BIT1 0) (BIT1 0).
Definition term710 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term755 (x0 : int) := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term197 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_le x0 x2) /\ (int_lt x1 x3)) -> int_lt (int_add x0 x1) (int_add x2 x3).
Definition term644 (x0 : int) (x1 : int) := int_add (int_mul x1 (int_sub (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))) x1.
Definition term72 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term91 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term593 (x0 : int) (x1 : int) := forall y0 : int, ((int_lt x1 x0) /\ (int_le x0 y0)) -> int_lt x1 y0.
Definition term291 (x0 : int) (x1 : int) := and (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))).
Definition term17 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term300 (x0 : int) (x1 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1)).
Definition term270 (x0 : int) := ((fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div y0 y1) y2) = (div y0 (int_mul y1 y2))) x0) /\ ((fun y0 : int => forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1))) x0).
Definition term538 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2))))).
Definition term711 (x0 : int) := real_add (real_of_int x0) (real_of_int x0).
Definition term521 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2))).
Definition term599 (x0 : int) (x1 : int) := fun y0 : int => (int_lt x0 y0) /\ (int_le y0 x1).
Definition term764 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term746 (x0 : int) := real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term700 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term485 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_mul x1 (int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2))).
Definition term651 (x0 : int) (x1 : int) := ~ (~ ((int_le x0 (int_abs x0)) /\ (int_le (int_of_num (NUMERAL 0)) (int_abs x1)))).
Definition term220 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x1 = (int_add (int_mul x0 x2) x3)) /\ ((int_le (int_of_num (NUMERAL 0)) x3) /\ (int_lt x3 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term15 (x0 : int) (x1 : int) := ~ ((int_add (int_mul x0 (int_sub x1 (int_of_num (NUMERAL (BIT1 0))))) x0) = (int_mul x0 x1)).
Definition term412 (x0 : int) (x1 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1)))).
Definition term353 (x0 : int) (x1 : int) (x2 : int) := @eq int (rem x0 (int_mul x1 x2)).
Definition term656 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term549 (x0 : int) (x1 : int) (x2 : int) := ((~ (~ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1)))))) \/ (real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))) -> False) -> ~ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1)))))) \/ (real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))).
Definition term457 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0))))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))) -> False) -> ~ ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0))))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term388 (x0 : int) (x1 : int) := ~ (x0 = (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1)))).
Definition term461 (x0 : int) (x1 : int) (x2 : int) := ((x1 = (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))) /\ (int_lt (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)) (int_abs (int_mul x2 x0))))) -> ((div x1 (int_mul x2 x0)) = (div (div x1 x2) x0)) /\ ((rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2))).
Definition term307 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term177 (x0 : int) (x1 : int) := (fun y0 : int => (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0))) x1.
Definition term586 (x0 : int) (x1 : int) (x2 : int) := and (int_le (int_of_num (NUMERAL 0)) (int_mul x1 (rem (div x0 x1) x2))).
Definition term793 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term500 (x0 : int) (x1 : int) (x2 : int) := or (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))))).
Definition term462 (x0 : int) (x1 : int) (x2 : int) := int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2).
Definition term105 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x1)).
Definition term707 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term211 (x0 : int) (x1 : int) := int_sub x0 (int_mul (div x0 x1) x1).
Definition term503 (x0 : int) (x1 : int) (x2 : int) := real_le (real_of_int (int_add (int_add (int_mul (div (div x2 x1) x0) (int_mul x1 x0)) (int_add (int_mul x1 (int_sub (div x2 x1) (int_mul (div (div x2 x1) x0) x0))) (int_sub x2 (int_mul (div x2 x1) x1)))) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x2).
Definition term87 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term95 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term128 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term40 := real_of_num (NUMERAL (BIT1 0)).
Definition term471 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_add x2 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul (div (div x2 x1) x0) (int_mul x1 x0)) (int_add (int_mul x1 (int_sub (div x2 x1) (int_mul (div (div x2 x1) x0) x0))) (int_sub x2 (int_mul (div x2 x1) x1))))) \/ (int_le (int_add (int_add (int_mul (div (div x2 x1) x0) (int_mul x1 x0)) (int_add (int_mul x1 (int_sub (div x2 x1) (int_mul (div (div x2 x1) x0) x0))) (int_sub x2 (int_mul (div x2 x1) x1)))) (int_of_num (NUMERAL (BIT1 0)))) x2).
Definition term776 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term765 (x0 : int) := and (real_ge (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term750 (x0 : int) := and (real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term16 (x0 : int) (x1 : int) := (int_le (int_add (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x1 x0)) \/ (int_le (int_add (int_mul x1 x0) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1)).
Definition term63 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)).
Definition term726 := BIT0 (BIT1 0).
Definition term540 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))).
Definition term435 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x0 x1)))).
Definition term247 (x0 : int -> Prop) (x1 : int -> Prop) := (forall y0 : int, x0 y0) /\ (forall y0 : int, x1 y0).
Definition term571 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> int_le (int_of_num (NUMERAL 0)) (int_add x0 x1).
Definition term811 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term150 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term505 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term417 (x0 : int) (x1 : int) := real_of_int (int_add (int_add (int_mul x1 (div x0 x1)) (int_sub x0 (int_mul (div x0 x1) x1))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term648 (x0 : int) (x1 : int) := int_le (int_add (int_mul x0 (int_sub (int_abs x1) (int_of_num (NUMERAL (BIT1 0))))) x0) (int_abs (int_mul x0 x1)).
Definition term378 (x0 : int) := (fun y0 : int => (int_mul y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term333 (x0 : int) := (fun y0 : int => (div y0 (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) x0.
Definition term420 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))).
Definition term241 (x0 : int) := ~ (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term788 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term787 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term626 (x0 : int) (x1 : int) (x2 : int) := int_le x0 (int_sub x1 x2).
Definition term47 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_sub (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term713 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term59 (x0 : int) (x1 : int) := int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term695 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term472 (x0 : int) (x1 : int) (x2 : int) := int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul (div (div x1 x2) x0) (int_mul x2 x0)) (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))).
Definition term382 (x0 : int) (x1 : int) := int_mul x1 (div x0 x1).
Definition term567 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_mul x0 x1).
Definition term342 := or (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term670 (x0 : int) := real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term742 (x0 : int) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term447 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term736 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term223 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term294 (x0 : int) := fun y0 : int => ((fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0) /\ ((fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem x0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div x0 y1) y2)) (rem x0 y1))) y0).
Definition term272 := fun y0 : int => ((fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0) /\ ((fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (rem y1 (int_mul y2 y3)) = (int_add (int_mul y2 (rem (div y1 y2) y3)) (rem y1 y2))) y0).
Definition term817 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term774 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term164 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term530 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x0) (real_of_int (div (div x2 x1) x0))))) (real_mul (real_of_int x1) (real_of_int (div x2 x1)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x2 x1)))) (real_of_int x2)).
Definition term576 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> (int_le (int_of_num (NUMERAL 0)) (int_mul x0 x1)) = True.
Definition term574 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> (int_le (int_of_num (NUMERAL 0)) (int_add x0 x1)) = True.
Definition term347 := div (int_of_num (NUMERAL 0)).
Definition term409 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)).
Definition term29 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term539 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))).
Definition term465 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)).
Definition term769 (x0 : int) (x1 : int) := ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term463 (x0 : int) (x1 : int) (x2 : int) := int_mul x1 (int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2)).
Definition term332 (x0 : int) := rem x0 (int_of_num (NUMERAL 0)).
Definition term535 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2)))).
Definition term724 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term585 (x0 : int) (x1 : int) (x2 : int) := int_le (int_of_num (NUMERAL 0)) (int_mul x1 (rem (div x0 x1) x2)).
Definition term556 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term739 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0).
Definition term706 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term783 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term39 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term210 (x0 : int) (x1 : int) := (fun y0 : int => (rem x0 y0) = (int_sub x0 (int_mul (div x0 y0) y0))) x1.
Definition term314 (x0 : int) (x1 : int) (x2 : int) := ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y0) = (div x0 (int_mul x1 y0))) x2) /\ ((fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y0)) = (int_add (int_mul x1 (rem (div x0 x1) y0)) (rem x0 x1))) x2).
Definition term689 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term508 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term85 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term9 (x0 : int) (x1 : int) (x2 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le (int_of_num (NUMERAL 0)) y2)) -> int_le (int_mul y0 y2) (int_mul y1 y2)) -> int_le (int_mul x0 x2) (int_mul x1 x2).
Definition term330 (x0 : int) := div (int_of_num (NUMERAL 0)) x0.
Definition term536 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int (div (div x2 x0) x1)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_mul (real_of_int x1) (real_of_int (div (div x2 x0) x1))))) (real_of_int x2)).
Definition term481 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_mul (div (div x0 x1) x2) (int_mul x1 x2))).
Definition term650 (x0 : int) (x1 : int) := ((int_le x0 (int_abs x0)) /\ (int_le (int_of_num (NUMERAL 0)) (int_abs x1))) -> int_le (int_mul x0 (int_abs x1)) (int_mul (int_abs x0) (int_abs x1)).
Definition term222 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term234 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term741 (x0 : int) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)).
Definition term501 (x0 : int) (x1 : int) (x2 : int) := or (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2)))))).
Definition term413 (x0 : int) (x1 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1))))).
Definition term534 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_of_int x1) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2))).
Definition term331 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL 0))) = y0) x0.
Definition term184 (x0 : int) := forall y0 : int, (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0) = (int_lt x0 y0).
Definition term639 (x0 : int) (x1 : int) (x2 : int) := int_lt (rem (div x0 x1) x2) (int_abs x2).
Definition term454 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term464 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x1 (int_sub (div x0 x1) (int_mul (div (div x0 x1) x2) x2))).
Definition term337 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term665 (x0 : int) := real_abs (real_of_int x0).
Definition term395 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term722 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term408 (x0 : int) (x1 : int) := real_mul (real_of_int (div x0 x1)) (real_of_int x1).
Definition term399 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x1 (div x0 x1))) (real_of_int (int_sub x0 (int_mul (div x0 x1) x1))).
Definition term647 (x0 : int) (x1 : int) := int_le (int_mul x0 (int_abs x1)).
Definition term143 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term754 (x0 : int) := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term238 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term640 (x0 : int) (x1 : int) := int_lt (rem x0 x1) (int_abs x1).
Definition term697 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term701 (x0 : int) := or (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term132 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term12 (x0 : int) (x1 : int) := int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1.
Definition term444 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term350 := int_mul (int_of_num (NUMERAL 0)).
Definition term709 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term772 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term110 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term796 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term73 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term368 (x0 : int) (x1 : int) (x2 : int) := and ((int_lt (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) x2) = (div x0 (int_mul x1 x2))).
Definition term313 (x0 : int) (x1 : int) (x2 : int) := and ((int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) x2) = (div x0 (int_mul x1 x2))).
Definition term67 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)).
Definition term814 := real_ge (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term153 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term653 (x0 : int) (x1 : int) := ~ ((int_le x0 (int_abs x0)) /\ (int_le (int_of_num (NUMERAL 0)) (int_abs x1))).
Definition term498 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2)))).
Definition term80 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term324 (x0 : int) := forall y0 : int, (int_le x0 y0) = ((int_lt x0 y0) \/ (x0 = y0)).
Definition term679 (x0 : int) (x1 : int) := (real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_abs (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term308 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y1)) = (int_add (int_mul x1 (rem (div x0 x1) y1)) (rem x0 x1))) y0.
Definition term303 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0.
Definition term44 (x0 : int) := real_mul (real_of_int x0).
Definition term380 (x0 : int) (x1 : int) := div (div x0 x1) (int_of_num (NUMERAL 0)).
Definition term352 (x0 : int) (x1 : int) (x2 : int) := rem x0 (int_mul x1 x2).
Definition term149 := real_add (real_of_num (NUMERAL 0)).
Definition term643 (x0 : int) (x1 : int) (x2 : int) := int_lt (int_add (int_mul x2 (rem (div x0 x2) x1)) (rem x0 x2)) (int_add (int_mul x2 (int_sub (int_abs x1) (int_of_num (NUMERAL (BIT1 0))))) x2).
Definition term822 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_abs (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) -> False.
Definition term548 (x0 : int) (x1 : int) (x2 : int) := (~ (~ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1)))))) \/ (real_le (real_add (real_add (real_mul (real_of_int (div (div x2 x1) x0)) (real_mul (real_of_int x1) (real_of_int x0))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int (div x2 x1)) (real_mul (real_of_int (div (div x2 x1) x0)) (real_of_int x0)))) (real_sub (real_of_int x2) (real_mul (real_of_int (div x2 x1)) (real_of_int x1))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))) -> False.
Definition term456 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0))))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))) -> False.
Definition term172 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_add (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int x0))) \/ (real_le (real_add (real_mul (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x1)))))) -> False.
Definition term828 (x0 : int) (x1 : int) (x2 : int) := int_lt (int_add (int_mul x1 (rem (div x0 x1) x2)) (rem x0 x1)) (int_abs (int_mul x1 x2)).
Definition term661 (x0 : int) := int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term65 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term52 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term139 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term344 := (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) \/ True.
Definition term696 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term309 (x0 : int) (x1 : int) := forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (rem x0 (int_mul x1 y1)) = (int_add (int_mul x1 (rem (div x0 x1) y1)) (rem x0 x1))) y0.
Definition term304 (x0 : int) (x1 : int) := forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) x1) -> (div (div x0 x1) y1) = (div x0 (int_mul x1 y1))) y0.
Definition term806 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term731 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term126 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term158 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term25 := int_of_num (NUMERAL (BIT1 0)).
Definition term64 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term572 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_add x0 x1).
Definition term383 (x0 : int) (x1 : int) := int_add (int_mul x1 (div x0 x1)).
Definition term794 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term458 (x0 : int) (x1 : int) := ~ ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0))))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term475 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_mul (div (div x1 x2) x0) (int_mul x2 x0))) (real_of_int (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2)))).
Definition term286 (x0 : int) := fun y0 : int => (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem x0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div x0 y1) y2)) (rem x0 y1))) y0.
Definition term281 (x0 : int) := fun y0 : int => (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (div (div x0 y1) y2) = (div x0 (int_mul y1 y2))) y0.
Definition term262 := fun y0 : int => (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (rem y1 (int_mul y2 y3)) = (int_add (int_mul y2 (rem (div y1 y2) y3)) (rem y1 y2))) y0.
Definition term255 := fun y0 : int => (fun y1 : int => forall y2 : int, forall y3 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (div (div y1 y2) y3) = (div y1 (int_mul y2 y3))) y0.
Definition term365 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ False.
Definition term431 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int (div x1 x0)))) (real_of_int x1).
Definition term41 := NUMERAL (BIT1 0).
Definition term425 (x0 : int) (x1 : int) := (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0))))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_int (div x1 x0))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x0)) (real_of_int x0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term583 (x0 : int) (x1 : int) (x2 : int) := int_le (int_of_num (NUMERAL 0)) (rem (div x0 x1) x2).
Definition term98 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term770 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term792 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term518 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_of_int (div x0 x1)) (real_mul (real_of_int x2) (real_of_int (div (div x0 x1) x2))).
Definition term624 (x0 : int) (x1 : int) := forall y0 : int, (int_le x0 (int_sub x1 y0)) = (int_le (int_add x0 y0) x1).
Definition term27 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0)))))) (real_of_int x1).
Definition term509 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_mul (real_of_int (div (div x1 x2) x0)) (real_mul (real_of_int x2) (real_of_int x0))) (real_add (real_mul (real_of_int x2) (real_sub (real_of_int (div x1 x2)) (real_mul (real_of_int (div (div x1 x2) x0)) (real_of_int x0)))) (real_sub (real_of_int x1) (real_mul (real_of_int (div x1 x2)) (real_of_int x2))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term421 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_sub (real_of_int x0) (real_mul (real_of_int (div x0 x1)) (real_of_int x1)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term373 (x0 : int) (x1 : int) (x2 : int) := True -> (rem x1 (int_mul x2 x0)) = (int_add (int_mul x2 (rem (div x1 x2) x0)) (rem x1 x2)).
Definition term83 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term356 (x0 : int) (x1 : int) (x2 : int) := rem (div x0 x1) x2.
Definition term786 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term781 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term403 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))).
Definition term777 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term432 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x0 x1))).
Definition term438 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_of_int x1) (real_of_int (div x0 x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_int (div x0 x1))))).
Definition term601 (x0 : int) := forall y0 : int, (exists y1 : int, (int_lt x0 y1) /\ (int_le y1 y0)) -> int_lt x0 y0.
Definition term483 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add (int_mul x2 (int_sub (div x1 x2) (int_mul (div (div x1 x2) x0) x0))) (int_sub x1 (int_mul (div x1 x2) x2))).
Definition term357 (x0 : int) := rem (int_of_num (NUMERAL 0)) x0.
Definition term20 (x0 : int) (x1 : int) := int_add (int_add (int_mul x1 (int_sub x0 (int_of_num (NUMERAL (BIT1 0))))) x1) (int_of_num (NUMERAL (BIT1 0))).
