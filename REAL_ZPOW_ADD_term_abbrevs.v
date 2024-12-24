Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term283 (x0 : real) := forall y0 : real, ((real_inv x0) = (real_inv y0)) = (x0 = y0).
Definition term52 (x0 : int) (x1 : int) := int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_neg x0) (int_add x0 x1)).
Definition term551 (x0 : real) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> (fun y0 : nat => fun y1 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) x1 x2.
Definition term258 (x0 : int) (x1 : int) := real_ge (real_sub (real_neg (real_add (real_neg (real_of_int x1)) (real_of_int x0))) (real_add (real_add (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term614 (x0 : real) (x1 : nat) := @eq real (real_zpow x0 (int_of_num x1)).
Definition term212 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term68 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_of_int x0) (real_of_int x1)).
Definition term273 (x0 : real) (x1 : int) := (fun y0 : int => (real_inv (real_zpow x0 y0)) = (real_zpow x0 (int_neg y0))) x1.
Definition term336 (x0 : real) := fun y0 : int => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1)).
Definition term323 := fun y0 : int => forall y1 : int, (int_neg (int_add y0 y1)) = (int_add (int_neg y0) (int_neg y1)).
Definition term112 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term15 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))) x2.
Definition term337 (x0 : real) (x1 : int) := (fun y0 : int => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1))) x1.
Definition term333 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term385 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num x2)).
Definition term490 (x0 : real) (x1 : nat) := fun y0 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num x1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 x1))).
Definition term451 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 y0))).
Definition term150 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term463 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term140 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term641 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x0 = (Nat.add x1 x3)) = x4) -> (x4 -> ((real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = x5) -> ((x0 = (Nat.add x1 x3)) -> (real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = (x4 -> x5).
Definition term609 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((x3 = (Nat.add x1 x0)) = x4) -> (x4 -> ((real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = x5) -> ((x3 = (Nat.add x1 x0)) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = (x4 -> x5).
Definition term76 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term307 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : a1, forall y2 : a0, y0 y2 y1)) x0.
Definition term352 (x0 : nat) (x1 : real) := forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y0)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y0)).
Definition term344 (x0 : nat) (x1 : real) := forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y0)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y0)).
Definition term338 (x0 : int) (x1 : real) := forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add x0 y0)) = (real_mul (real_zpow x1 x0) (real_zpow x1 y0)).
Definition term31 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_neg x0) (int_add x0 x1))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term95 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term448 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_add (int_of_num x1) (int_neg (int_of_num x2)))).
Definition term423 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_neg (int_of_num x2)))).
Definition term427 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_neg (int_of_num (Nat.add x0 y0)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term388 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_of_num (Nat.add x0 y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0))).
Definition term130 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term598 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) := (x3 = (Nat.add x1 x0)) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3)).
Definition term597 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) := ((fun y0 : nat => x3 = (Nat.add x1 y0)) x0) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3)).
Definition term217 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1).
Definition term5 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term483 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 y0)))) x2.
Definition term278 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0))) x1.
Definition term84 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term118 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term101 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term539 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2))).
Definition term319 (x0 : int) := fun y0 : int => (int_neg (int_add x0 y0)) = (int_add (int_neg x0) (int_neg y0)).
Definition term516 (x0 : nat) (x1 : real) := fun y0 : nat => (fun y1 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y1))) y0.
Definition term102 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term191 (x0 : int) (x1 : int) := real_of_int (int_add (int_neg x0) x1).
Definition term554 (x0 : nat) (x1 : real) := fun y0 : nat => (Peano.le x0 y0) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term592 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0).
Definition term382 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_of_num (Nat.add x1 x2)).
Definition term75 (x0 : nat) := real_neg (real_of_num x0).
Definition term556 (x0 : nat) (x1 : real) := forall y0 : nat, (Peano.le x0 y0) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term251 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term63 (x0 : Prop) := ~ (~ x0).
Definition term83 := real_of_num (NUMERAL 0).
Definition term636 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (x0 = (real_of_num (NUMERAL 0))) = False.
Definition term129 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term650 (x0 : real) (x1 : nat) := real_mul (real_mul (real_inv (real_pow x0 x1)) (real_pow x0 x1)).
Definition term190 (x0 : int) (x1 : int) := real_neg (real_of_int (int_add (int_neg x0) x1)).
Definition term203 (x0 : int) (x1 : int) := int_le (int_add (int_add (int_neg x1) x0) (int_of_num (NUMERAL (BIT1 0)))) (int_neg (int_add (int_neg x0) x1)).
Definition term222 (x0 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) -> x1.
Definition term590 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.add x1 y1)) y0.
Definition term419 (x0 : nat) (x1 : nat) := int_neg (int_add (int_of_num x0) (int_of_num x1)).
Definition term21 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term290 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_inv x0) = (real_inv y0))) x1.
Definition term461 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_of_num x2))).
Definition term383 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_add (int_of_num x1) (int_of_num x2))).
Definition term450 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num x2)))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 x2))).
Definition term90 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term219 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)).
Definition term104 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term65 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x1) (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term588 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term444 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term66 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term503 (x0 : real) := (fun y0 : Prop => y0 = (forall y1 : nat, forall y2 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2)))) ((forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)))).
Definition term649 (x0 : real) (x1 : nat) := real_mul (real_inv (real_pow x0 x1)) (real_pow x0 x1).
Definition term146 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term652 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) := (x0 = (Nat.add x1 x3)) -> ((real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = True.
Definition term193 (x0 : int) (x1 : int) := real_add (real_neg (real_of_int x0)) (real_of_int x1).
Definition term262 (x0 : real) (x1 : int) := real_zpow x0 (int_neg x1).
Definition term25 (x0 : int) (x1 : int) := int_le (int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term134 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x1) (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term329 (x0 : int) := (fun y0 : int => forall y1 : int, (int_add (int_neg y0) (int_neg y1)) = (int_neg (int_add y0 y1))) x0.
Definition term301 (x0 : int) := (fun y0 : int => forall y1 : int, (int_add y0 y1) = (int_add y1 y0)) x0.
Definition term581 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((real_zpow x1 (int_add (int_neg (int_of_num x2)) (int_of_num x0))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 x2)))).
Definition term218 (x0 : int) (x1 : int) := real_neg (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)).
Definition term205 (x0 : int) (x1 : int) := int_add (int_add (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term123 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term562 (x0 : real) := (forall y0 : nat, forall y1 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) = ((real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y0)))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))).
Definition term561 (x0 : real) := (forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1) = ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1).
Definition term502 (x0 : real) := (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))).
Definition term497 (x0 : real) := (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y0)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y0)))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))).
Definition term474 (x0 : real) := (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1)))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))).
Definition term357 (x0 : real) := (forall y0 : nat, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) y1)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 y1))) /\ (forall y0 : nat, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) y1)) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 y1))).
Definition term292 (x0 : type1605) := (forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1).
Definition term280 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term64 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1)))))).
Definition term460 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2).
Definition term78 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term55 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term439 (x0 : real) (x1 : nat) := real_mul (real_pow x0 x1).
Definition term596 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.add x1 x2)).
Definition term434 := fun y0 : real => (forall y1 : nat, (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_of_num (Nat.add y1 y2))) = (real_mul (real_zpow y0 (int_of_num y1)) (real_zpow y0 (int_of_num y2)))) /\ (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_zpow y0 (int_of_num y1)) (real_zpow y0 (int_neg (int_of_num y2)))))) /\ (forall y1 : nat, (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_zpow y0 (int_neg (int_of_num y1))) (real_zpow y0 (int_of_num y2)))) /\ (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_neg (int_of_num (Nat.add y1 y2)))) = (real_mul (real_zpow y0 (int_neg (int_of_num y1))) (real_zpow y0 (int_neg (int_of_num y2)))))).
Definition term260 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x1)) (real_of_int x0))) \/ (real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))))))) -> False) -> ~ ((real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x1)) (real_of_int x0))) \/ (real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))))).
Definition term48 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term569 (x0 : real) := ((forall y0 : nat, forall y1 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) = ((real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y0)))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)))) -> forall y0 : nat, forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term534 (x0 : real) := ((forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1) = ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1)) -> forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1.
Definition term291 (x0 : type1605) := ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term587 (x0 : nat) (x1 : real) (x2 : nat) := forall y0 : nat, ((fun y1 : nat => x2 = (Nat.add x0 y1)) y0) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term305 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term239 (x0 : int) (x1 : int) := real_sub (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term517 (x0 : nat) (x1 : real) := forall y0 : nat, (fun y1 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y1))) y0.
Definition term128 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term386 (x0 : real) := imp (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term583 (x0 : nat) (x1 : real) (x2 : nat) := (exists y0 : nat, x2 = (Nat.add x0 y0)) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term537 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) x1 x2.
Definition term482 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => fun y1 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1)))) x1 x2.
Definition term197 (x0 : int) (x1 : int) := real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term40 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_neg x0) (int_add x0 x1))).
Definition term151 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term306 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term88 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term120 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term202 (x0 : int) (x1 : int) := or (real_le (real_add (real_neg (real_add (real_neg (real_of_int x1)) (real_of_int x0))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_of_int x1))).
Definition term176 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term110 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term405 (x0 : nat) (x1 : real) := fun y0 : nat => (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_of_num y0).
Definition term368 (x0 : nat) (x1 : real) := fun y0 : nat => (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_of_num y0).
Definition term331 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term411 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y0)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y0))) (int_neg (int_of_num x2)).
Definition term374 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y0)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y0))) (int_neg (int_of_num x2)).
Definition term213 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))).
Definition term519 (x0 : nat) (x1 : real) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> forall y0 : nat, (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term491 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y2)))) y0 x1.
Definition term430 (x0 : real) := fun y0 : nat => (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_neg (int_of_num (Nat.add y0 y1)))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 (int_neg (int_of_num y1))))).
Definition term392 (x0 : real) := fun y0 : nat => (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_of_num (Nat.add y0 y1))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_neg (int_of_num y1))))).
Definition term505 (x0 : real) := @eq Prop (((forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)))) = (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)))).
Definition term233 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term245 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term187 (x0 : int) (x1 : int) := real_of_int (int_add (int_neg (int_add (int_neg x0) x1)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term381 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_add (int_of_num x1) (int_of_num x2)).
Definition term298 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term47 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term261 (x0 : int) (x1 : int) := ~ ((real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x1)) (real_of_int x0))) \/ (real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))))).
Definition term49 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1).
Definition term458 (x0 : real) (x1 : nat) := real_mul (real_inv (real_pow x0 x1)).
Definition term447 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_inv (real_pow x1 x2)).
Definition term308 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term464 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term550 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term192 (x0 : int) (x1 : int) := real_add (real_of_int (int_neg x0)) (real_of_int x1).
Definition term100 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term440 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> True.
Definition term237 (x0 : int) (x1 : int) := real_sub (real_add (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term215 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x1)) (real_of_int x0))) \/ (real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1)))))).
Definition term77 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term27 (x0 : int) (x1 : int) := int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0))).
Definition term143 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term67 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term322 (x0 : int) := forall y0 : int, (int_add (int_neg x0) (int_neg y0)) = (int_neg (int_add x0 y0)).
Definition term86 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term527 (x0 : real) := fun y0 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (fun y1 : nat => forall y2 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0.
Definition term56 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term435 := forall y0 : real, forall y1 : int, forall y2 : int, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add y1 y2)) = (real_mul (real_zpow y0 y1) (real_zpow y0 y2)).
Definition term316 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term310 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term288 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_inv y0) = (real_inv y1)).
Definition term287 := forall y0 : real, forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1).
Definition term271 := forall y0 : real, forall y1 : int, (real_inv (real_zpow y0 y1)) = (real_zpow y0 (int_neg y1)).
Definition term270 := forall y0 : real, forall y1 : int, (real_zpow y0 (int_neg y1)) = (real_inv (real_zpow y0 y1)).
Definition term1 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term145 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term582 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term529 (x0 : real) := @eq Prop (forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))).
Definition term528 (x0 : real) := @eq Prop (forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (fun y1 : nat => forall y2 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0).
Definition term515 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0))).
Definition term514 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (fun y1 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y1))) y0).
Definition term195 (x0 : int) (x1 : int) := real_add (real_of_int (int_neg (int_add (int_neg x0) x1))).
Definition term633 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term223 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term317 (x0 : int) (x1 : int) := int_neg (int_add x0 x1).
Definition term149 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term117 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term201 (x0 : int) (x1 : int) := or (int_le (int_add (int_neg (int_add (int_neg x1) x0)) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_neg x0) x1)).
Definition term625 (x0 : nat) (x1 : nat) (x2 : real) := fun y0 : nat => (x0 = (Nat.add x1 y0)) -> (real_pow x2 y0) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 y0)).
Definition term89 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term81 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term198 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_neg (int_add (int_neg x0) x1)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term19 (x0 : int) (x1 : int) := int_add (int_neg x0) (int_add x0 x1).
Definition term446 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_neg (int_of_num x2))).
Definition term321 (x0 : int) := forall y0 : int, (int_neg (int_add x0 y0)) = (int_add (int_neg x0) (int_neg y0)).
Definition term399 (x0 : nat) (x1 : real) (x2 : int) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) x2)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 x2)).
Definition term362 (x0 : nat) (x1 : real) (x2 : int) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) x2)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 x2)).
Definition term114 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term543 (x0 : real) (x1 : nat) := forall y0 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 x1)) (real_pow x0 y0))) = ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num x1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 x1))).
Definition term525 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) x1.
Definition term13 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1.
Definition term589 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.add x1 y0)) x2.
Definition term196 (x0 : int) (x1 : int) := real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))).
Definition term324 := fun y0 : int => forall y1 : int, (int_add (int_neg y0) (int_neg y1)) = (int_neg (int_add y0 y1)).
Definition term577 (x0 : real) (x1 : nat) := real_inv (real_inv (real_pow x0 x1)).
Definition term156 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))))))) -> False) -> ~ ((real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))))).
Definition term144 := real_le (real_of_num (NUMERAL 0)).
Definition term28 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term433 := fun y0 : real => forall y1 : int, forall y2 : int, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add y1 y2)) = (real_mul (real_zpow y0 y1) (real_zpow y0 y2)).
Definition term152 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term634 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term299 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term646 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term557 (x0 : real) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1.
Definition term544 (x0 : real) := fun y0 : nat => forall y1 : nat, ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1) = ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y1 y0).
Definition term296 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term441 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term189 (x0 : int) (x1 : int) := real_of_int (int_neg (int_add (int_neg x0) x1)).
Definition term619 (x0 : nat) (x1 : real) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add x2 y0)) -> (real_zpow x1 (int_of_num y0)) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 (Nat.add x2 y0))).
Definition term398 (x0 : nat) (x1 : real) (x2 : int) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y0)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y0))) x2.
Definition term361 (x0 : nat) (x1 : real) (x2 : int) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y0)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y0))) x2.
Definition term242 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term16 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add x1 x2).
Definition term297 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term449 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_add (int_of_num x1) (int_neg (int_of_num x2))).
Definition term57 (x0 : int) := real_add (real_of_int x0).
Definition term402 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y0)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y0))).
Definition term365 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : int, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y0)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y0))).
Definition term471 (x0 : nat) (x1 : real) := (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0))) /\ True.
Definition term206 (x0 : int) (x1 : int) := real_of_int (int_add (int_add (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term602 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term154 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term565 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) x1 y0.
Definition term484 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y2)))) x1 y0.
Definition term627 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term186 (x0 : int) (x1 : int) := int_add (int_neg (int_add (int_neg x0) x1)) (int_of_num (NUMERAL (BIT1 0))).
Definition term268 := fun y0 : real => forall y1 : int, (real_zpow y0 (int_neg y1)) = (real_inv (real_zpow y0 y1)).
Definition term71 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term629 (x0 : real) := (fun y0 : real => forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term311 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1))) x0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term39 (x0 : int) (x1 : int) := real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1)).
Definition term303 (x0 : int) (x1 : int) := (fun y0 : int => (int_add x0 y0) = (int_add y0 x0)) x1.
Definition term426 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_neg (int_of_num (Nat.add x0 x2)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num x2)))).
Definition term42 (x0 : nat) := real_of_int (int_of_num x0).
Definition term412 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x2)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num x2)))).
Definition term375 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num x2)))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_neg (int_of_num x2)))).
Definition term286 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_inv y0) = (real_inv y1)).
Definition term107 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (x0 : int) (x1 : int) := (real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1)))).
Definition term103 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term313 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0))) x1.
Definition term96 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term225 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term538 (x0 : real) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => fun y1 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) x1 x2).
Definition term493 (x0 : real) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y2) (int_neg (int_of_num y3)))) = (real_mul (real_pow x0 y2) (real_inv (real_pow x0 y3)))) y1 y0.
Definition term204 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_neg x1) x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_neg (int_add (int_neg x0) x1))).
Definition term396 (x0 : nat) (x1 : real) := (forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_neg (int_of_num y0))).
Definition term359 (x0 : nat) (x1 : real) := (forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_neg (int_of_num y0))).
Definition term335 (x0 : real) := (forall y0 : nat, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_neg (int_of_num y0))).
Definition term29 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term481 (x0 : real) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1)))) x1.
Definition term492 (x0 : real) (x1 : nat) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num x1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 x1))).
Definition term465 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term452 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 y0))).
Definition term428 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_neg (int_of_num (Nat.add x0 y0)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term416 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term408 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num y0))).
Definition term389 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_of_num (Nat.add x0 y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0))).
Definition term379 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term371 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_of_num y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0))).
Definition term79 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term488 (x0 : real) := @eq Prop (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1)))).
Definition term487 (x0 : real) := @eq Prop (forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y2) (int_neg (int_of_num y3)))) = (real_mul (real_pow x0 y2) (real_inv (real_pow x0 y3)))) y0 y1).
Definition term266 (x0 : real) := forall y0 : int, (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0)).
Definition term384 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_of_num (Nat.add x1 x2))).
Definition term521 (x0 : real) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term466 (x0 : nat) (x1 : real) := and (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0))).
Definition term410 (x0 : nat) (x1 : real) := and (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num y0)))).
Definition term394 (x0 : real) := and (forall y0 : nat, (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_of_num (Nat.add y0 y1))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_neg (int_of_num y1)))))).
Definition term390 (x0 : nat) (x1 : real) := and (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_of_num (Nat.add x0 y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0)))).
Definition term373 (x0 : nat) (x1 : real) := and (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_of_num y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0)))).
Definition term188 (x0 : int) (x1 : int) := real_add (real_of_int (int_neg (int_add (int_neg x0) x1))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term470 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_mul (real_inv (real_pow x1 x0)) (real_inv (real_pow x1 x2))).
Definition term3 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term153 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term125 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term300 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term178 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0)) x1.
Definition term453 (x0 : nat) (x1 : real) := True /\ (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 y0)))).
Definition term69 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x1)).
Definition term183 (x0 : int) (x1 : int) := (int_le (int_add (int_neg (int_add (int_neg x0) x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_neg x1) x0)) \/ (int_le (int_add (int_add (int_neg x1) x0) (int_of_num (NUMERAL (BIT1 0)))) (int_neg (int_add (int_neg x0) x1))).
Definition term85 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term332 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term564 (x0 : real) := imp ((forall y0 : nat, forall y1 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) = ((real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y0)))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)))).
Definition term563 (x0 : real) := imp ((forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1) = ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1)).
Definition term438 (x0 : real) (x1 : nat) := real_mul (real_zpow x0 (int_of_num x1)).
Definition term232 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term70 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term302 (x0 : int) := forall y0 : int, (int_add x0 y0) = (int_add y0 x0).
Definition term330 (x0 : int) (x1 : int) := (fun y0 : int => (int_add (int_neg x0) (int_neg y0)) = (int_neg (int_add x0 y0))) x1.
Definition term275 (x0 : real) := real_inv (real_inv x0).
Definition term653 (x0 : real) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add x2 x3)) -> ((real_pow x0 x3) = (real_mul (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x2)) (real_pow x0 x3))) = True) -> ((x1 = (Nat.add x2 x3)) -> (real_pow x0 x3) = (real_mul (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x2)) (real_pow x0 x3))) = ((x1 = (Nat.add x2 x3)) -> True).
Definition term570 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_of_num x2))).
Definition term254 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term265 (x0 : real) := fun y0 : int => (real_inv (real_zpow x0 y0)) = (real_zpow x0 (int_neg y0)).
Definition term437 (x0 : nat) (x1 : real) (x2 : nat) := @eq real (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term568 (x0 : real) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1.
Definition term560 (x0 : real) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term559 (x0 : real) := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1.
Definition term547 (x0 : real) := forall y0 : nat, forall y1 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) = ((real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y0))).
Definition term546 (x0 : real) := forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1) = ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y1 y0).
Definition term532 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term495 (x0 : real) := forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y0)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y0))).
Definition term479 (x0 : real) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y2) (int_neg (int_of_num y3)))) = (real_mul (real_pow x0 y2) (real_inv (real_pow x0 y3)))) y1 y0.
Definition term478 (x0 : real) := forall y0 : nat, forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y2) (int_neg (int_of_num y3)))) = (real_mul (real_pow x0 y2) (real_inv (real_pow x0 y3)))) y0 y1.
Definition term477 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y1 y0.
Definition term473 (x0 : real) := forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term455 (x0 : real) := forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1))).
Definition term356 (x0 : real) := forall y0 : nat, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) y1)) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 y1)).
Definition term348 (x0 : real) := forall y0 : nat, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) y1)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 y1)).
Definition term293 (x0 : type1605) := forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term167 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1)).
Definition term166 := forall y0 : nat, forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1)).
Definition term12 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term424 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_neg (int_of_num (Nat.add x1 x2)))).
Definition term644 (x0 : real) (x1 : nat) := (~ ((real_pow x0 x1) = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv (real_pow x0 x1)) (real_pow x0 x1)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term234 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term131 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term282 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_inv x0) = (real_inv y0)).
Definition term60 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term250 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term249 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term179 (x0 : int) (x1 : int) := ~ (~ ((int_neg (int_add (int_neg x1) x0)) = (int_add (int_neg x0) x1))).
Definition term648 (x0 : real) (x1 : nat) := ~ ((real_pow x0 x1) = (real_of_num (NUMERAL 0))).
Definition term628 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term526 (x0 : real) (x1 : nat) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (fun y0 : nat => forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) x1.
Definition term511 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0))) x2.
Definition term342 (x0 : real) := @eq Prop (forall y0 : int, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1))).
Definition term194 (x0 : int) (x1 : int) := real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term210 (x0 : int) (x1 : int) := real_add (real_add (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term263 (x0 : real) (x1 : int) := real_inv (real_zpow x0 x1).
Definition term97 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term594 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((exists y0 : nat, x2 = (Nat.add x0 y0)) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2))).
Definition term593 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x2 = (Nat.add x0 y1)) y0) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2))).
Definition term240 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term216 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term137 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term274 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term309 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y1 y0.
Definition term163 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0)).
Definition term575 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_zpow x0 (int_neg (int_add (int_neg (int_of_num x1)) (int_of_num x2)))).
Definition term229 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term228 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term157 (x0 : int) (x1 : int) := ~ ((real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))))).
Definition term600 (x0 : nat) (x1 : real) (x2 : nat) := fun y0 : nat => (x2 = (Nat.add x0 y0)) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term631 (x0 : real) (x1 : nat) := (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term17 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_pow x1 x2).
Definition term618 (x0 : nat) (x1 : real) (x2 : nat) (x3 : nat) := (x0 = (Nat.add x2 x3)) -> (real_zpow x1 (int_of_num x3)) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 (Nat.add x2 x3))).
Definition term443 := forall y0 : nat, True.
Definition term285 := fun y0 : real => forall y1 : real, ((real_inv y0) = (real_inv y1)) = (y0 = y1).
Definition term243 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term513 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (fun y1 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y1))) y0.
Definition term138 (x0 : int) (x1 : int) := real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))).
Definition term126 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 (x0 : int) (x1 : int) := int_neg (int_add (int_neg x0) x1).
Definition term409 (x0 : nat) (x1 : real) := and (forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_of_num y0)).
Definition term372 (x0 : nat) (x1 : real) := and (forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_of_num y0)).
Definition term349 (x0 : real) := and (forall y0 : nat, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_of_num y0)).
Definition term520 (x0 : real) := fun y0 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term295 (x0 : type1605) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1) -> ((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term584 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) -> x1.
Definition term247 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term623 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x0)) (real_pow x1 x2).
Definition term340 (x0 : real) := forall y0 : int, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1)).
Definition term326 := forall y0 : int, forall y1 : int, (int_add (int_neg y0) (int_neg y1)) = (int_neg (int_add y0 y1)).
Definition term325 := forall y0 : int, forall y1 : int, (int_neg (int_add y0 y1)) = (int_add (int_neg y0) (int_neg y1)).
Definition term304 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term289 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_inv y0) = (real_inv y1))) x0.
Definition term276 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1))) x0.
Definition term93 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term397 (x0 : nat) (x1 : real) := fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y0)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y0)).
Definition term360 (x0 : nat) (x1 : real) := fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y0)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y0)).
Definition term135 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term462 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_of_num x2)).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) -> y1) = (forall y2 : a0, (y0 y2) -> y1)) x0.
Definition term148 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term54 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term87 := S (Nat.add 0 0).
Definition term580 (x0 : nat) (x1 : nat) := int_neg (int_add (int_neg (int_of_num x0)) (int_of_num x1)).
Definition term121 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term475 := fun y0 : real => (forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_pow y0 y1) (real_inv (real_pow y0 y2)))) /\ (forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow y0 y1)) (real_pow y0 y2))).
Definition term442 := fun y0 : nat => True.
Definition term518 (x0 : nat) (x1 : real) := forall y0 : nat, (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term14 (x0 : nat) (x1 : real) := forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0)).
Definition term41 (x0 : int) (x1 : int) := real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))).
Definition term61 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))).
Definition term248 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term404 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num x2))).
Definition term367 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_of_num x2))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num x2))).
Definition term34 (x0 : int) (x1 : int) := real_add (real_of_int (int_neg x0)) (real_of_int (int_add x0 x1)).
Definition term72 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term267 (x0 : real) := forall y0 : int, (real_inv (real_zpow x0 y0)) = (real_zpow x0 (int_neg y0)).
Definition term99 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term585 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) -> x1.
Definition term23 (x0 : int) (x1 : int) := (int_le (int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_neg x0) (int_add x0 x1))).
Definition term643 (x0 : real) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.add x2 x3)) -> ((real_pow x0 x3) = (real_mul (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x2)) (real_pow x0 x3))) = x4) -> ((x1 = (Nat.add x2 x3)) -> (real_pow x0 x3) = (real_mul (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x2)) (real_pow x0 x3))) = ((x1 = (Nat.add x2 x3)) -> x4).
Definition term611 (x0 : real) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.add x2 x3)) -> ((real_zpow x0 (int_add (int_neg (int_of_num x2)) (int_of_num x1))) = (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x1))) = x4) -> ((x1 = (Nat.add x2 x3)) -> (real_zpow x0 (int_add (int_neg (int_of_num x2)) (int_of_num x1))) = (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x1))) = ((x1 = (Nat.add x2 x3)) -> x4).
Definition term142 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term639 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((x0 = (Nat.add x1 x3)) = x4) -> (x4 -> ((real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = y0) -> ((x0 = (Nat.add x1 x3)) -> (real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = (x4 -> y0).
Definition term607 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((x3 = (Nat.add x1 x0)) = x4) -> (x4 -> ((real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = y0) -> ((x3 = (Nat.add x1 x0)) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = (x4 -> y0).
Definition term603 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term269 := fun y0 : real => forall y1 : int, (real_inv (real_zpow y0 y1)) = (real_zpow y0 (int_neg y1)).
Definition term343 (x0 : real) (x1 : nat) := (fun y0 : int => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1))) (int_of_num x1).
Definition term504 (x0 : real) := @eq Prop ((fun y0 : Prop => y0 = (forall y1 : nat, forall y2 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2)))) ((forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) /\ (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))))).
Definition term162 (x0 : nat) := forall y0 : nat, (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term351 (x0 : real) (x1 : nat) := (fun y0 : int => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y0 y1)) = (real_mul (real_zpow x0 y0) (real_zpow x0 y1))) (int_neg (int_of_num x1)).
Definition term566 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) x1 y0.
Definition term485 (x0 : real) (x1 : nat) := forall y0 : nat, (fun y1 : nat => fun y2 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y2)))) x1 y0.
Definition term345 (x0 : real) := fun y0 : nat => (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_of_num y0).
Definition term314 (x0 : real) (x1 : nat) := real_zpow x0 (int_neg (int_of_num x1)).
Definition term522 (x0 : real) := forall y0 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (fun y1 : nat => forall y2 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0.
Definition term508 (x0 : nat) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (fun y1 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y1))) y0.
Definition term591 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.add x1 y1)) y0.
Definition term567 (x0 : real) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1.
Definition term486 (x0 : real) := fun y0 : nat => forall y1 : nat, (fun y2 : nat => fun y3 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y2) (int_neg (int_of_num y3)))) = (real_mul (real_pow x0 y2) (real_inv (real_pow x0 y3)))) y0 y1.
Definition term105 := real_mul (real_of_num (NUMERAL 0)).
Definition term637 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((x0 = (Nat.add x1 x3)) = y0) -> (y0 -> ((real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = y1) -> ((x0 = (Nat.add x1 x3)) -> (real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = (y0 -> y1).
Definition term605 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((x3 = (Nat.add x1 x0)) = y0) -> (y0 -> ((real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = y1) -> ((x3 = (Nat.add x1 x0)) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = (y0 -> y1).
Definition term604 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term420 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.add x0 x1)).
Definition term207 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_neg x0) x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term33 (x0 : int) (x1 : int) := real_of_int (int_add (int_neg x0) (int_add x0 x1)).
Definition term425 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num x2))).
Definition term334 (x0 : real) := forall y0 : int, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) y0.
Definition term255 (x0 : int) (x1 : int) := real_ge (real_sub (real_neg (real_add (real_neg (real_of_int x1)) (real_of_int x0))) (real_add (real_add (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term169 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0))) x1.
Definition term574 (x0 : real) (x1 : nat) (x2 : nat) := @eq real (real_inv (real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_of_num x2)))).
Definition term387 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_of_num (Nat.add x0 x2))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num x2))).
Definition term18 (x0 : int) (x1 : int) := ~ (~ ((int_add (int_neg x0) (int_add x0 x1)) = x1)).
Definition term536 (x0 : real) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) x1.
Definition term59 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term224 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term457 (x0 : real) (x1 : nat) := real_mul (real_zpow x0 (int_neg (int_of_num x1))).
Definition term227 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term498 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_neg (int_of_num x1)).
Definition term115 (x0 : int) := real_sub (real_of_int x0).
Definition term617 (x0 : nat) (x1 : real) (x2 : nat) (x3 : nat) := ((x0 = (Nat.add x2 x3)) -> ((real_zpow x1 (int_add (int_neg (int_of_num x2)) (int_of_num x0))) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 x0))) = ((real_zpow x1 (int_of_num x3)) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 (Nat.add x2 x3))))) -> ((x0 = (Nat.add x2 x3)) -> (real_zpow x1 (int_add (int_neg (int_of_num x2)) (int_of_num x0))) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 x0))) = ((x0 = (Nat.add x2 x3)) -> (real_zpow x1 (int_of_num x3)) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 (Nat.add x2 x3)))).
Definition term91 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term401 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : int, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) y0).
Definition term364 (x0 : nat) (x1 : real) := @eq Prop (forall y0 : int, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) y0).
Definition term341 (x0 : real) := @eq Prop (forall y0 : int, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) y0).
Definition term354 (x0 : real) := fun y0 : nat => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) y1)) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 y1)).
Definition term346 (x0 : real) := fun y0 : nat => forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) y1)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 y1)).
Definition term230 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term279 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term109 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term510 (x0 : nat) (x1 : real) := fun y0 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0)).
Definition term432 (x0 : real) := (forall y0 : nat, (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_of_num (Nat.add y0 y1))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_neg (int_of_num y1)))))) /\ (forall y0 : nat, (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_neg (int_of_num (Nat.add y0 y1)))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 (int_neg (int_of_num y1)))))).
Definition term429 (x0 : nat) (x1 : real) := (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num y0)))) /\ (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_neg (int_of_num (Nat.add x0 y0)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num y0))))).
Definition term417 (x0 : nat) (x1 : real) := (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num y0)))) /\ (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num y0))))).
Definition term391 (x0 : nat) (x1 : real) := (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_of_num (Nat.add x0 y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0)))) /\ (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_neg (int_of_num y0))))).
Definition term380 (x0 : nat) (x1 : real) := (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_of_num y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0)))) /\ (forall y0 : nat, (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_neg (int_of_num y0))))).
Definition term20 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term571 (x0 : nat) (x1 : real) (x2 : nat) := real_inv (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term36 (x0 : int) := real_neg (real_of_int x0).
Definition term74 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term182 (x0 : int) (x1 : int) := ~ ((int_neg (int_add (int_neg x1) x0)) = (int_add (int_neg x0) x1)).
Definition term116 (x0 : int) (x1 : int) := real_sub (real_of_int x1) (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term507 (x0 : Prop) (x1 : nat -> Prop) := x0 -> forall y0 : nat, x1 y0.
Definition term640 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x0 = (Nat.add x1 x3)) = x4) -> (x4 -> ((real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = y0) -> ((x0 = (Nat.add x1 x3)) -> (real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = (x4 -> y0)) x5.
Definition term608 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((x3 = (Nat.add x1 x0)) = x4) -> (x4 -> ((real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = y0) -> ((x3 = (Nat.add x1 x0)) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = (x4 -> y0)) x5.
Definition term256 (x0 : int) (x1 : int) := real_sub (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))).
Definition term549 (x0 : real) := and (forall y0 : nat, forall y1 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) = ((real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y0)))).
Definition term548 (x0 : real) := and (forall y0 : nat, forall y1 : nat, ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y0 y1) = ((fun y2 : nat => fun y3 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y2)) (int_of_num y3))) = (real_mul (real_inv (real_pow x0 y2)) (real_pow x0 y3))) y1 y0)).
Definition term501 (x0 : real) := and (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))).
Definition term496 (x0 : real) := and (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y0)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y0)))).
Definition term456 (x0 : real) := and (forall y0 : nat, forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1)))).
Definition term350 (x0 : real) := and (forall y0 : nat, forall y1 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) y1)) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 y1))).
Definition term632 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))).
Definition term9 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term209 (x0 : int) (x1 : int) := real_add (real_add (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term586 (x0 : nat) (x1 : real) (x2 : nat) := (exists y0 : nat, (fun y1 : nat => x2 = (Nat.add x0 y1)) y0) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) -> y0) = (forall y1 : a0, (x0 y1) -> y0).
Definition term599 (x0 : nat) (x1 : real) (x2 : nat) := fun y0 : nat => ((fun y1 : nat => x2 = (Nat.add x0 y1)) y0) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term221 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term98 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term200 (x0 : int) (x1 : int) := real_le (real_add (real_neg (real_add (real_neg (real_of_int x1)) (real_of_int x0))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term459 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num x2)).
Definition term500 (x0 : nat) := int_neg (int_of_num x0).
Definition term530 (x0 : real) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0.
Definition term573 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_neg (int_add (int_neg (int_of_num x1)) (int_of_num x2))).
Definition term24 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term327 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1))) x0.
Definition term175 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term168 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1))) x0.
Definition term533 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> forall y0 : nat, forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term226 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term328 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0))) x1.
Definition term318 (x0 : int) (x1 : int) := int_add (int_neg x0) (int_neg x1).
Definition term578 (x0 : real) (x1 : nat) := real_mul (real_inv (real_inv (real_pow x0 x1))).
Definition term199 (x0 : int) (x1 : int) := real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term621 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term11 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.add y1 y2)) = (real_mul (real_pow y0 y1) (real_pow y0 y2))) x0.
Definition term622 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_inv (real_pow x1 x0)) (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term407 (x0 : nat) (x1 : real) := forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_of_num y0).
Definition term370 (x0 : nat) (x1 : real) := forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_of_num y0).
Definition term294 (x0 : type1605) := (((forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> x0 y0 y1)) -> forall y0 : nat, forall y1 : nat, x0 y0 y1) -> forall y0 : nat, forall y1 : nat, x0 y0 y1.
Definition term160 (x0 : nat) := fun y0 : nat => (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term184 (x0 : int) (x1 : int) := int_le (int_add (int_neg (int_add (int_neg x1) x0)) (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_neg x0) x1).
Definition term277 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term616 (x0 : nat) (x1 : real) (x2 : nat) (x3 : nat) := (x0 = (Nat.add x2 x3)) -> ((real_zpow x1 (int_add (int_neg (int_of_num x2)) (int_of_num x0))) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 x0))) = ((real_zpow x1 (int_of_num x3)) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 (Nat.add x2 x3)))).
Definition term476 := forall y0 : real, (forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_pow y0 y1) (real_inv (real_pow y0 y2)))) /\ (forall y1 : nat, forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow y0 y1)) (real_pow y0 y2))).
Definition term436 := forall y0 : real, (forall y1 : nat, (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_of_num (Nat.add y1 y2))) = (real_mul (real_zpow y0 (int_of_num y1)) (real_zpow y0 (int_of_num y2)))) /\ (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_zpow y0 (int_of_num y1)) (real_zpow y0 (int_neg (int_of_num y2)))))) /\ (forall y1 : nat, (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_zpow y0 (int_neg (int_of_num y1))) (real_zpow y0 (int_of_num y2)))) /\ (forall y2 : nat, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_zpow y0 (int_neg (int_of_num (Nat.add y1 y2)))) = (real_mul (real_zpow y0 (int_neg (int_of_num y1))) (real_zpow y0 (int_neg (int_of_num y2)))))).
Definition term94 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term241 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term220 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term38 (x0 : int) := real_add (real_neg (real_of_int x0)).
Definition term111 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term422 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_neg (int_of_num (Nat.add x1 x2))).
Definition term355 (x0 : real) := forall y0 : nat, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_neg (int_of_num y0)).
Definition term108 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term44 := real_of_num (NUMERAL (BIT1 0)).
Definition term312 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) -> x1.
Definition term208 (x0 : int) (x1 : int) := real_add (real_of_int (int_add (int_neg x0) x1)).
Definition term272 (x0 : real) := (fun y0 : real => forall y1 : int, (real_inv (real_zpow y0 y1)) = (real_zpow y0 (int_neg y1))) x0.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term133 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term238 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term315 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term244 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term480 (x0 : real) := fun y0 : nat => fun y1 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1))).
Definition term161 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0)).
Definition term468 (x0 : nat) (x1 : real) (x2 : nat) := real_inv (real_mul (real_pow x1 x0) (real_pow x1 x2)).
Definition term214 (x0 : int) (x1 : int) := (real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x1)) (real_of_int x0))) \/ (real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1)))).
Definition term281 (x0 : real) := fun y0 : real => ((real_inv x0) = (real_inv y0)) = (x0 = y0).
Definition term10 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term127 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term147 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term541 (x0 : real) (x1 : nat) := fun y0 : nat => ((real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 x1)) (real_pow x0 y0))) = ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num x1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 x1))).
Definition term445 (x0 : Prop) := forall y0 : nat, x0.
Definition term624 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) := (x0 = (Nat.add x1 x3)) -> (real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3)).
Definition term30 (x0 : int) (x1 : int) := real_of_int (int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term642 (x0 : real) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.add x2 x3)) = (x1 = (Nat.add x2 x3))) -> ((x1 = (Nat.add x2 x3)) -> ((real_pow x0 x3) = (real_mul (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x2)) (real_pow x0 x3))) = x4) -> ((x1 = (Nat.add x2 x3)) -> (real_pow x0 x3) = (real_mul (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x2)) (real_pow x0 x3))) = ((x1 = (Nat.add x2 x3)) -> x4).
Definition term610 (x0 : real) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((x1 = (Nat.add x2 x3)) = (x1 = (Nat.add x2 x3))) -> ((x1 = (Nat.add x2 x3)) -> ((real_zpow x0 (int_add (int_neg (int_of_num x2)) (int_of_num x1))) = (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x1))) = x4) -> ((x1 = (Nat.add x2 x3)) -> (real_zpow x0 (int_add (int_neg (int_of_num x2)) (int_of_num x1))) = (real_mul (real_inv (real_pow x0 x2)) (real_pow x0 x1))) = ((x1 = (Nat.add x2 x3)) -> x4).
Definition term252 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 (x0 : int) := real_of_int (int_neg x0).
Definition term635 (x0 : real) := real_mul (real_inv x0) x0.
Definition term231 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term43 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term579 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((real_zpow x1 (int_neg (int_add (int_neg (int_of_num x0)) (int_of_num x2)))) = (real_mul (real_pow x1 x0) (real_inv (real_pow x1 x2)))).
Definition term164 := fun y0 : nat => forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1)).
Definition term257 (x0 : int) (x1 : int) := real_sub (real_neg (real_add (real_neg (real_of_int x1)) (real_of_int x0))) (real_add (real_add (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term553 (x0 : real) (x1 : nat) := fun y0 : nat => (Peano.le x1 y0) -> (fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) x1 y0.
Definition term92 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term645 (x0 : real) := and (x0 = (real_of_num (NUMERAL 0))).
Definition term469 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_inv (real_pow x1 x0)) (real_inv (real_pow x1 x2)).
Definition term431 (x0 : real) := forall y0 : nat, (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_neg (int_of_num (Nat.add y0 y1)))) = (real_mul (real_zpow x0 (int_neg (int_of_num y0))) (real_zpow x0 (int_neg (int_of_num y1))))).
Definition term393 (x0 : real) := forall y0 : nat, (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_of_num (Nat.add y0 y1))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_of_num y1)))) /\ (forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_zpow x0 (int_of_num y0)) (real_zpow x0 (int_neg (int_of_num y1))))).
Definition term542 (x0 : real) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) x1 y0) = ((fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0 x1).
Definition term51 (x0 : int) (x1 : int) := or (real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term612 (x0 : nat) := int_add (int_neg (int_of_num x0)).
Definition term626 (x0 : nat) (x1 : nat) (x2 : real) := forall y0 : nat, (x0 = (Nat.add x1 y0)) -> (real_pow x2 y0) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 y0)).
Definition term620 (x0 : nat) (x1 : real) (x2 : nat) := forall y0 : nat, (x0 = (Nat.add x2 y0)) -> (real_zpow x1 (int_of_num y0)) = (real_mul (real_inv (real_pow x1 x2)) (real_pow x1 (Nat.add x2 y0))).
Definition term601 (x0 : nat) (x1 : real) (x2 : nat) := forall y0 : nat, (x2 = (Nat.add x0 y0)) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term415 (x0 : nat) (x1 : real) := forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_neg (int_of_num y0)).
Definition term378 (x0 : nat) (x1 : real) := forall y0 : nat, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_neg (int_of_num y0)).
Definition term418 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term467 (x0 : real) (x1 : nat) (x2 : nat) := real_inv (real_pow x0 (Nat.add x1 x2)).
Definition term555 (x0 : real) (x1 : nat) := forall y0 : nat, (Peano.le x1 y0) -> (fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) x1 y0.
Definition term403 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y0)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y0))) (int_of_num x2).
Definition term366 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y0)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y0))) (int_of_num x2).
Definition term139 (x0 : int) (x1 : int) := real_sub (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term489 (x0 : real) (x1 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y2)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y2)))) y0 x1.
Definition term499 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num x0)) (int_of_num x1).
Definition term53 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_neg x0) (int_add x0 x1))).
Definition term236 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term58 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term284 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_inv x0) = (real_inv y0)).
Definition term595 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => x0 = (Nat.add x1 y0)) x2).
Definition term320 (x0 : int) := fun y0 : int => (int_add (int_neg x0) (int_neg y0)) = (int_neg (int_add x0 y0)).
Definition term159 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term235 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term347 (x0 : real) := forall y0 : nat, (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_of_num y0).
Definition term113 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term535 (x0 : real) := fun y0 : nat => fun y1 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term119 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term264 (x0 : real) := fun y0 : int => (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0)).
Definition term353 (x0 : real) := fun y0 : nat => (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) (int_neg (int_of_num y0)).
Definition term177 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term615 (x0 : real) (x1 : nat) (x2 : nat) := real_mul (real_inv (real_pow x0 x1)) (real_pow x0 (Nat.add x1 x2)).
Definition term80 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term73 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term576 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_inv (real_inv (real_pow x1 x0))) (real_inv (real_pow x1 x2)).
Definition term136 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term638 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = (Nat.add x1 x3)) = y0) -> (y0 -> ((real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = y1) -> ((x0 = (Nat.add x1 x3)) -> (real_pow x2 x3) = (real_mul (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x1)) (real_pow x2 x3))) = (y0 -> y1)) x4.
Definition term606 (x0 : nat) (x1 : nat) (x2 : real) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x3 = (Nat.add x1 x0)) = y0) -> (y0 -> ((real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = y1) -> ((x3 = (Nat.add x1 x0)) -> (real_zpow x2 (int_add (int_neg (int_of_num x1)) (int_of_num x3))) = (real_mul (real_inv (real_pow x2 x1)) (real_pow x2 x3))) = (y0 -> y1)) x4.
Definition term122 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term181 (x0 : int) (x1 : int) := int_add (int_neg x0) x1.
Definition term400 (x0 : nat) (x1 : real) := fun y0 : int => (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) y0.
Definition term363 (x0 : nat) (x1 : real) := fun y0 : int => (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) y0.
Definition term531 (x0 : real) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0.
Definition term132 := real_add (real_of_num (NUMERAL 0)).
Definition term523 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> forall y0 : nat, (fun y1 : nat => forall y2 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0.
Definition term509 (x0 : nat) (x1 : real) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> forall y0 : nat, (fun y1 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y1))) y0.
Definition term613 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1)).
Definition term259 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_add (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x1)) (real_of_int x0))) \/ (real_le (real_add (real_add (real_neg (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_add (real_neg (real_of_int x0)) (real_of_int x1))))))) -> False.
Definition term155 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))))))) -> False.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term46 (x0 : int) (x1 : int) := real_add (real_add (real_neg (real_of_int x0)) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term211 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term540 (x0 : real) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) x1 y0) = ((fun y1 : nat => fun y2 : nat => (real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y2))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y2))) y0 x1).
Definition term246 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term22 (x0 : int) (x1 : int) := ~ ((int_add (int_neg x0) (int_add x0 x1)) = x1).
Definition term395 (x0 : nat) (x1 : real) := forall y0 : int, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) y0.
Definition term358 (x0 : nat) (x1 : real) := forall y0 : int, (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) y0.
Definition term106 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term141 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term421 (x0 : real) (x1 : nat) (x2 : nat) := real_zpow x0 (int_add (int_neg (int_of_num x1)) (int_neg (int_of_num x2))).
Definition term32 := int_of_num (NUMERAL (BIT1 0)).
Definition term506 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 -> x1 y0.
Definition term647 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term253 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term413 (x0 : nat) (x1 : real) := fun y0 : nat => (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) y1)) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 y1))) (int_neg (int_of_num y0)).
Definition term376 (x0 : nat) (x1 : real) := fun y0 : nat => (fun y1 : int => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) y1)) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 y1))) (int_neg (int_of_num y0)).
Definition term158 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term339 (x0 : real) := fun y0 : int => (fun y1 : int => forall y2 : int, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add y1 y2)) = (real_mul (real_zpow x0 y1) (real_zpow x0 y2))) y0.
Definition term558 (x0 : real) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term545 (x0 : real) := fun y0 : nat => forall y1 : nat, ((real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1))) = ((real_zpow x0 (int_add (int_neg (int_of_num y1)) (int_of_num y0))) = (real_mul (real_inv (real_pow x0 y1)) (real_pow x0 y0))).
Definition term524 (x0 : real) := fun y0 : nat => forall y1 : nat, (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term494 (x0 : real) := fun y0 : nat => forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y1) (int_neg (int_of_num y0)))) = (real_mul (real_pow x0 y1) (real_inv (real_pow x0 y0))).
Definition term472 (x0 : real) := fun y0 : nat => forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_neg (int_of_num y0)) (int_of_num y1))) = (real_mul (real_inv (real_pow x0 y0)) (real_pow x0 y1)).
Definition term454 (x0 : real) := fun y0 : nat => forall y1 : nat, (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_zpow x0 (int_add (int_of_num y0) (int_neg (int_of_num y1)))) = (real_mul (real_pow x0 y0) (real_inv (real_pow x0 y1))).
Definition term165 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1)).
Definition term572 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((real_inv (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2)))) = (real_inv (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)))).
Definition term45 := NUMERAL (BIT1 0).
Definition term414 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term406 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_zpow x1 (int_neg (int_of_num x0))) (real_zpow x1 (int_of_num y0))).
Definition term377 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_neg (int_of_num y0)))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_neg (int_of_num y0)))).
Definition term369 (x0 : nat) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num (NUMERAL 0)))) -> (real_zpow x1 (int_add (int_of_num x0) (int_of_num y0))) = (real_mul (real_zpow x1 (int_of_num x0)) (real_zpow x1 (int_of_num y0))).
Definition term552 (x0 : nat) (x1 : real) (x2 : nat) := (Peano.le x0 x2) -> (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num x2))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 x2)).
Definition term654 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add x1 x2)) -> True.
Definition term124 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : int) := real_add (real_of_int (int_neg x0)).
Definition term512 (x0 : nat) (x1 : real) (x2 : nat) := (~ (x1 = (real_of_num (NUMERAL 0)))) -> (fun y0 : nat => (real_zpow x1 (int_add (int_neg (int_of_num x0)) (int_of_num y0))) = (real_mul (real_inv (real_pow x1 x0)) (real_pow x1 y0))) x2.
Definition term630 (x0 : real) := forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
Definition term651 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 x1).
Definition term50 (x0 : int) (x1 : int) := or (int_le (int_add (int_add (int_neg x0) (int_add x0 x1)) (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term185 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_neg (int_add (int_neg x1) x0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_neg x0) x1)).
