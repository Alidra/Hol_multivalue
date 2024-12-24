Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term509 (x0 : int) (x1 : int) := (~ (int_lt (rem x0 x1) (int_abs x1))) -> int_lt (rem x0 x1) (int_abs x1).
Definition term519 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3))))).
Definition term499 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp (~ ((~ (x2 = x0)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))))).
Definition term438 := fun y0 : int => forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term425 := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term386 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1))).
Definition term120 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term195 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term355 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 (x0 : int) := (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) /\ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0)))).
Definition term440 (x0 : int) := (fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ ((int_abs y0) = y0)) x0.
Definition term318 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term399 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term326 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term71 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term398 (x0 : int -> Prop) := ~ (all x0).
Definition term472 := int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term527 := (~ False) -> False.
Definition term396 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) /\ (~ (int_lt (rem x0 x1) x1)).
Definition term385 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term83 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term175 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term19 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term264 (x0 : int) := real_ge (real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term245 (x0 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term239 (x0 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term272 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term252 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term140 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term97 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term115 (x0 : int) := real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term185 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term279 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term186 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term148 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term502 (x0 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) /\ (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term172 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term337 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term496 (x0 : int) (x1 : int) := and (~ (int_lt x0 x1)).
Definition term70 (x0 : nat) := real_neg (real_of_num x0).
Definition term265 (x0 : int) := real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term358 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term393 (x0 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0.
Definition term363 := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0.
Definition term347 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term17 := real_of_int (int_of_num (NUMERAL 0)).
Definition term61 (x0 : Prop) := ~ (~ x0).
Definition term18 := real_of_num (NUMERAL 0).
Definition term162 := real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term173 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term382 := (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term257 (x0 : int) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term10 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term249 (x0 : int) := real_sub (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term471 := (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) -> ~ (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term7 := int_of_num (NUMERAL 0).
Definition term29 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term104 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0)).
Definition term361 (x0 : int) := ((~ (~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) /\ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))))))) -> False) -> ~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) /\ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))))).
Definition term278 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term184 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term146 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term281 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term188 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term154 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term376 := (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term480 (x0 : int) (x1 : int) (x2 : int) := (~ (x2 = x0)) \/ (~ (int_lt x1 x2)).
Definition term95 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term63 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term516 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x2 = x0))) /\ (~ (~ (int_lt x1 x2))).
Definition term405 (x0 : int) := fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) /\ (~ (int_lt (rem x0 y0) y0)).
Definition term289 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0).
Definition term174 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term402 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0) x1.
Definition term314 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term259 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term212 (x0 : int) := (fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_neg (real_of_int x0)).
Definition term163 := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term240 (x0 : int) := real_sub (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term442 (x0 : int) := (fun y0 : int => forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1))))) x0.
Definition term408 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1) x0.
Definition term437 (x0 : int) := forall y0 : int, ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term492 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term99 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term232 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1) x2.
Definition term77 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term364 (x0 : Prop) := (~ x0) -> False.
Definition term413 (x0 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x0)) \/ ((int_abs x0) = x0).
Definition term389 := forall y0 : int, ~ (int_lt y0 y0).
Definition term1 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_abs x0) = x0.
Definition term199 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term168 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))).
Definition term96 (x0 : int) := real_sub (real_of_int x0) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term177 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term488 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((~ (x2 = x0)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3)))).
Definition term503 (x0 : int) := ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) /\ ((~ (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) /\ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term50 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term205 (x0 : int) := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term94 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term310 (x0 : int) := ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))))).
Definition term404 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem x0 y1) y1) y0).
Definition term226 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term352 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term444 (x0 : int) (x1 : int) := ~ (int_lt (rem x0 x1) x1).
Definition term420 (x0 : int) (x1 : int) := (~ (~ (x1 = (int_of_num (NUMERAL 0))))) \/ ((x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term510 (x0 : int) (x1 : int) := ~ (int_lt (rem x0 x1) (int_abs x1)).
Definition term24 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term101 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term246 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term102 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term136 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term299 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term522 (x0 : int) (x1 : int) := ((int_abs x1) = x1) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term319 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term500 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((x2 = x0) /\ ((~ (int_lt x0 x1)) /\ (int_lt x2 x3))).
Definition term276 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term274 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term182 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term181 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term144 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term138 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))).
Definition term112 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term501 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x1 = x0) /\ ((~ (int_lt x0 x3)) /\ (int_lt x1 x2))) -> ~ (x2 = x3).
Definition term468 := (~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)))) -> (int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)).
Definition term432 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (rem x0 x1).
Definition term462 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term194 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term304 (x0 : int) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term40 (x0 : int) := real_add (real_abs (real_of_int x0)).
Definition term3 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_abs x0) = x0)).
Definition term452 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x2 = x0) -> (~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))).
Definition term41 (x0 : int) := real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term354 := real_lt (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term331 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term293 (x0 : int) := real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term238 (x0 : int) := real_ge (real_of_int x0).
Definition term269 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term260 (x0 : int) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term216 (x0 : int) := (real_gt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term456 (x0 : Prop) := (~ x0) -> x0.
Definition term285 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term87 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term42 (x0 : int) := real_le (real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))).
Definition term211 (x0 : int) := fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term525 (x0 : int) (x1 : int) := (~ (int_lt (rem x0 x1) x1)) -> int_lt (rem x0 x1) x1.
Definition term469 := ~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))).
Definition term342 (x0 : int) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term287 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term73 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term307 (x0 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term309 (x0 : int) := or ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term306 (x0 : int) := or ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term223 (x0 : int) := or ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term208 (x0 : int) := (fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_abs (real_of_int x0)).
Definition term311 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term487 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term390 := fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0.
Definition term268 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term409 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1) x0).
Definition term56 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0)).
Definition term291 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)).
Definition term113 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term518 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x2 = x0) /\ ((x3 = x1) /\ (int_lt x2 x3)).
Definition term237 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term142 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term255 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term51 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term233 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term313 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term219 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term220 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_int x0)).
Definition term489 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (~ (x2 = x0))) /\ (~ ((int_lt x0 x1) \/ (~ (int_lt x2 x3)))).
Definition term57 (x0 : int) := (real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))).
Definition term106 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term231 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : int) := real_of_int (int_abs x0).
Definition term443 (x0 : int) (x1 : int) := (fun y0 : int => ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0))))) x1.
Definition term317 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term431 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1))).
Definition term506 (x0 : int) (x1 : int) := (int_lt (rem x0 x1) (int_abs x1)) \/ (x1 = (int_of_num (NUMERAL 0))).
Definition term277 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term183 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term145 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term155 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term180 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term137 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term25 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term254 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term474 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term236 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term165 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_int x0)).
Definition term464 (x0 : int) := ~ (~ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term383 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term340 (x0 : int) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term152 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term242 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term312 := real_le (real_of_num (NUMERAL 0)).
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term320 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term6 (x0 : int) := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term463 (x0 : int) := (~ (~ (int_lt (int_of_num (NUMERAL 0)) x0))) -> (int_abs x0) = x0.
Definition term493 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))).
Definition term415 := forall y0 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ ((int_abs y0) = y0).
Definition term121 (x0 : int) := and (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term460 (x0 : int) := @eq Prop ((~ (int_lt (int_of_num (NUMERAL 0)) x0)) \/ ((int_abs x0) = x0)).
Definition term286 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term520 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((x2 = x0) /\ ((x3 = x1) /\ (int_lt x2 x3))).
Definition term335 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term98 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term324 := real_lt (real_of_num (NUMERAL 0)).
Definition term391 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> int_lt (rem x0 x1) x1.
Definition term261 (x0 : int) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term524 (x0 : int) (x1 : int) := (((rem x0 x1) = (rem x0 x1)) /\ (((int_abs x1) = x1) /\ (int_lt (rem x0 x1) (int_abs x1)))) -> int_lt (rem x0 x1) x1.
Definition term52 (x0 : int) := real_add (real_of_int x0).
Definition term303 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term62 (x0 : int) := ~ (~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) /\ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0)))))).
Definition term107 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term35 (x0 : int) := real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term322 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term225 (x0 : int) := @eq Prop ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term280 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term448 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) \/ (~ (int_lt x2 x3)).
Definition term176 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term133 (x0 : int) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term16 (x0 : nat) := real_of_int (int_of_num x0).
Definition term241 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term497 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (int_lt x0 x1)) /\ (int_lt x2 x3).
Definition term191 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term372 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term4 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term187 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term84 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term217 (x0 : int) := (fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term5 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term125 (x0 : real) (x1 : real) (x2 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_ge (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term12 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term417 (x0 : int) (x1 : int) := (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term178 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term478 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((int_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3)))).
Definition term13 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term371 := (((~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> ((~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term230 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term466 (x0 : int) := imp (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term369 := ((~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term321 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term88 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term451 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))).
Definition term243 (x0 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term221 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term141 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term447 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_lt x2 x3) = (int_lt x0 x1)) -> (int_lt x0 x1) \/ (~ (int_lt x2 x3)).
Definition term301 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term169 (x0 : int) := real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term482 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((int_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3))))).
Definition term160 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term129 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term362 (x0 : int) := ~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) /\ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))))).
Definition term349 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term294 (x0 : int) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term36 (x0 : int) := real_add (real_of_int (int_abs x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term353 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term486 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term498 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x2 = x0) /\ ((~ (int_lt x0 x1)) /\ (int_lt x2 x3)).
Definition term275 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term308 (x0 : int) := or ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term526 (x0 : int) (x1 : int) := (int_lt (rem x0 x1) x1) -> False.
Definition term197 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term55 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term201 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term170 (x0 : int) := real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term271 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term258 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term445 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1)).
Definition term85 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term370 := (((~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term0 (x0 : int) := ~ (~ ((int_lt (int_of_num (NUMERAL 0)) x0) -> (int_abs x0) = x0)).
Definition term400 (x0 : int) := ~ (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0).
Definition term332 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term157 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term44 (x0 : int) := real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term27 (x0 : int) := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term523 (x0 : int) (x1 : int) := ((rem x0 x1) = (rem x0 x1)) /\ (((int_abs x1) = x1) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term46 (x0 : int) := or (real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term30 (x0 : int) := ~ ((int_abs x0) = x0).
Definition term214 (x0 : int) := and (real_gt (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term89 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term91 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term288 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term467 (x0 : int) := (~ ((int_abs x0) = x0)) -> (int_abs x0) = x0.
Definition term439 := forall y0 : int, forall y1 : int, ((y1 = (int_of_num (NUMERAL 0))) \/ (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1)))) /\ (((y1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem y0 y1))) /\ ((y1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term426 := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ ((y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term374 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1))).
Definition term365 := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1.
Definition term81 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term200 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term92 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term159 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term343 (x0 : int) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term357 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term328 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term300 (x0 : int) := real_ge (real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term253 (x0 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term316 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term49 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term158 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term143 := S (Nat.add 0 0).
Definition term513 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3)))).
Definition term282 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term74 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term441 (x0 : int) := (fun y0 : int => ~ (int_lt y0 y0)) x0.
Definition term421 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term72 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term366 := (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> False.
Definition term262 (x0 : int) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term397 (x0 : int) (x1 : int) := int_lt (rem x0 x1) x1.
Definition term139 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term284 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term76 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term507 (x0 : int) (x1 : int) := @eq Prop ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1))).
Definition term424 (x0 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term394 := fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1.
Definition term247 (x0 : int) := real_sub (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term368 := (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)) -> (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term218 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term213 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term209 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term206 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term126 (x0 : int) := (real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term59 (x0 : int) := and (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term109 (x0 : int) := real_sub (real_abs (real_of_int x0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term296 (x0 : int) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term505 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term341 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term32 (x0 : int) := int_le (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term33 (x0 : int) := real_le (real_of_int (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term9 (x0 : int) := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term430 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1))).
Definition term31 (x0 : int) := (int_le (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_abs x0)).
Definition term189 := real_mul (real_of_num (NUMERAL 0)).
Definition term135 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term207 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term491 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term153 := NUMERAL (BIT0 (BIT1 0)).
Definition term2 (x0 : int) := ~ ((int_lt (int_of_num (NUMERAL 0)) x0) -> (int_abs x0) = x0).
Definition term108 (x0 : int) := real_ge (real_sub (real_abs (real_of_int x0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term422 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term204 := and (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term210 (x0 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_int x0))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_neg (real_of_int x0)))).
Definition term54 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term470 := ~ (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term39 (x0 : int) := real_add (real_of_int (int_abs x0)).
Definition term373 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term367 := ~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1).
Definition term64 (x0 : int) := real_sub (real_of_int x0).
Definition term79 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term193 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term446 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term256 (x0 : int) := real_gt (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term26 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term266 (x0 : int) := real_neg (real_of_int x0).
Definition term403 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0) x1).
Definition term387 (x0 : int) := ~ (int_lt x0 x0).
Definition term69 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term248 := real_sub (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term395 (x0 : int) (x1 : int) := ~ ((int_lt (int_of_num (NUMERAL 0)) x1) -> int_lt (rem x0 x1) x1).
Definition term333 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term434 (x0 : int) (x1 : int) := and ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))).
Definition term435 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))) /\ (((x1 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 x1))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term222 (x0 : int) := or ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_of_int x0))).
Definition term377 := (forall y0 : int, ~ (int_lt y0 y0)) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term380 := (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))).
Definition term150 := Nat.add (BIT1 0) (BIT1 0).
Definition term131 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term67 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 (x0 : int) := or (int_le (int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term86 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term484 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ ((~ (x1 = x0)) \/ ((int_lt x0 x3) \/ (~ (int_lt x1 x2))))) -> ~ (x2 = x3).
Definition term457 (x0 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x0)) -> int_lt (int_of_num (NUMERAL 0)) x0.
Definition term47 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_abs x0).
Definition term228 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term8 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term132 (x0 : int) := real_add (real_of_int x0) (real_of_int x0).
Definition term459 (x0 : int) := ((int_abs x0) = x0) \/ (~ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term302 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term171 (x0 : int) := real_ge (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term263 (x0 : int) := real_ge (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term118 (x0 : int) := real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term234 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term229 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term388 := fun y0 : int => ~ (int_lt y0 y0).
Definition term511 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (int_lt x0 x1))))) -> int_lt x2 x3.
Definition term128 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term58 (x0 : int) := and (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term117 (x0 : int) := real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term508 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> int_lt (rem x0 x1) (int_abs x1).
Definition term436 (x0 : int) := fun y0 : int => ((y0 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0)))) /\ (((y0 = (int_of_num (NUMERAL 0))) \/ (int_le (int_of_num (NUMERAL 0)) (rem x0 y0))) /\ ((y0 = (int_of_num (NUMERAL 0))) \/ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term375 := imp (forall y0 : int, ~ (int_lt y0 y0)).
Definition term82 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term512 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3))).
Definition term454 (x0 : int) (x1 : int) := (~ ((rem x0 x1) = (rem x0 x1))) -> (rem x0 x1) = (rem x0 x1).
Definition term517 (x0 : int) (x1 : int) (x2 : int) := (x2 = x0) /\ (int_lt x1 x2).
Definition term267 (x0 : int) := real_add (real_neg (real_of_int x0)).
Definition term250 := real_sub (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term515 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x2 = x0)) \/ (~ (int_lt x1 x2))).
Definition term192 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term22 := real_of_num (NUMERAL (BIT1 0)).
Definition term329 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term203 (x0 : int) := and (real_ge (real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0))).
Definition term151 := BIT0 (BIT1 0).
Definition term481 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))))).
Definition term297 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term198 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term414 := fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ ((int_abs y0) = y0).
Definition term483 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x3 = x1)) \/ ((~ (x2 = x0)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3)))).
Definition term346 (x0 : int) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term416 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term461 (x0 : int) := @eq Prop (((int_abs x0) = x0) \/ (~ (int_lt (int_of_num (NUMERAL 0)) x0))).
Definition term479 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3)))).
Definition term458 (x0 : int) := ~ (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term504 (x0 : int) := (((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))) /\ ((~ (int_lt (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) /\ (int_lt (int_of_num (NUMERAL 0)) x0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term134 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term251 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term450 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term514 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3)))).
Definition term122 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term494 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (int_lt x0 x1)) /\ (~ (~ (int_lt x2 x3))).
Definition term43 (x0 : int) := real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term292 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term167 (x0 : int) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term298 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term161 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term356 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term327 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term315 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term351 (x0 : int) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term384 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0))).
Definition term495 (x0 : int) (x1 : int) := ~ (~ (int_lt x0 x1)).
Definition term123 (x0 : int) := ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_abs (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term455 (x0 : int) (x1 : int) := ~ ((rem x0 x1) = (rem x0 x1)).
Definition term348 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term149 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term429 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)).
Definition term164 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0).
Definition term127 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term336 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term21 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term103 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term305 (x0 : int) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term80 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term428 (x0 : int) (x1 : int) := int_add (int_mul (div x0 x1) x1) (rem x0 x1).
Definition term407 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y2) -> int_lt (rem y1 y2) y2) y0).
Definition term401 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem x0 y1) y1) y0).
Definition term427 (x0 : int) (x1 : int) := ((x1 = (int_of_num (NUMERAL 0))) \/ (x0 = (int_add (int_mul (div x0 x1) x1) (rem x0 x1)))) /\ ((x1 = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) (rem x0 x1)) /\ (int_lt (rem x0 x1) (int_abs x1)))).
Definition term166 (x0 : int) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_int x0)).
Definition term412 := exists y0 : int, exists y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) /\ (~ (int_lt (rem y0 y1) y1)).
Definition term423 (x0 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((x0 = (int_add (int_mul (div x0 y0) y0) (rem x0 y0))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem x0 y0)) /\ (int_lt (rem x0 y0) (int_abs y0)))).
Definition term270 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term244 (x0 : int) := real_ge (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : int) := real_abs (real_of_int x0).
Definition term53 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term147 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term433 (x0 : int) (x1 : int) := int_lt (rem x0 x1) (int_abs x1).
Definition term378 := imp (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0).
Definition term119 (x0 : int) := or (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term196 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term111 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term419 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term490 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term449 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x3 = x1) -> (int_lt x0 x1) \/ (~ (int_lt x2 x3)).
Definition term130 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term215 (x0 : int) := (real_gt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((fun y0 : real => (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) (real_neg (real_of_int x0))).
Definition term325 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term179 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term273 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term68 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term14 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term411 := fun y0 : int => exists y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) /\ (~ (int_lt (rem y0 y1) y1)).
Definition term202 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term477 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term75 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term418 (x0 : int) := or (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term345 (x0 : int) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term339 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term110 (x0 : int) := real_add (real_abs (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term235 := real_div (real_of_num (NUMERAL 0)).
Definition term224 (x0 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term476 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term20 := real_add (real_of_num (NUMERAL 0)).
Definition term521 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x0 = x2) /\ ((x1 = x3) /\ (int_lt x0 x1))) -> int_lt x2 x3.
Definition term360 (x0 : int) := (~ (~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) /\ ((real_le (real_add (real_abs (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_int x0))))))) -> False.
Definition term485 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))).
Definition term34 (x0 : int) := int_add (int_abs x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term379 := (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_abs y0) = y0) -> (forall y0 : int, ~ (int_lt y0 y0)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> (y0 = (int_add (int_mul (div y0 y1) y1) (rem y0 y1))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem y0 y1)) /\ (int_lt (rem y0 y1) (int_abs y1)))) -> False.
Definition term453 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3)))).
Definition term283 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term190 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term156 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term406 (x0 : int) := exists y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) /\ (~ (int_lt (rem x0 y0) y0)).
Definition term15 := int_of_num (NUMERAL (BIT1 0)).
Definition term350 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term48 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_abs x0)).
Definition term23 := NUMERAL (BIT1 0).
Definition term290 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term344 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term338 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term381 := imp (~ (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> int_lt (rem y0 y1) y1)).
Definition term465 (x0 : int) := imp (~ (~ (int_lt (int_of_num (NUMERAL 0)) x0))).
Definition term473 (x0 : Prop) := x0 -> ~ x0.
Definition term323 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term78 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term410 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y2) -> int_lt (rem y1 y2) y2) y0).
Definition term359 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_neg (real_of_num x1)).
Definition term295 (x0 : int) := real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term475 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3))).
Definition term392 (x0 : int) := fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> int_lt (rem x0 y0) y0.
Definition term334 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term116 (x0 : int) := real_ge (real_sub (real_abs (real_of_int x0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term330 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term227 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
