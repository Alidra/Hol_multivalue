Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term187 (x0 : real) (x1 : real -> Prop) := fun y0 : nat => (fun y1 : nat => ((x0 = (real_of_num y1)) /\ (~ (x1 x0))) /\ (forall y2 : nat, x1 (real_of_num y2))) y0.
Definition term357 := (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term651 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := exists y0 : real, (((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x2) /\ (forall y1 : real, (~ (real_le (real_of_num (x1 y1)) y1)) \/ (real_le x2 y1)))) /\ ((fun y1 : real => forall y2 : nat, ~ (real_le y1 (real_of_num y2))) y0).
Definition term223 (x0 : real -> Prop) := fun y0 : real => ~ (x0 y0).
Definition term153 (x0 : real -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))) x1.
Definition term435 := or (~ ((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0))).
Definition term834 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term261 (x0 : real) := real_sub (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term765 (x0 : real -> nat) (x1 : real) := (~ (real_le x1 (real_of_num (x0 x1)))) -> real_le (real_of_num (x0 x1)) x1.
Definition term273 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 := fun y0 : real -> Prop => (~ ((forall y1 : real, (exists y2 : nat, y1 = (real_of_num y2)) -> y0 y1) = (forall y1 : nat, y0 (real_of_num y1)))) -> False.
Definition term659 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := fun y0 : real => (((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x2) /\ (forall y1 : real, (~ (real_le (real_of_num (x1 y1)) y1)) \/ (real_le x2 y1)))) /\ ((fun y1 : real => forall y2 : nat, ~ (real_le y1 (real_of_num y2))) y0).
Definition term396 (x0 : real) := exists y0 : nat, real_le x0 (real_of_num y0).
Definition term4 (x0 : real -> Prop) := ~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0))).
Definition term244 (x0 : real -> Prop) := (fun y0 : real -> Prop => (~ ((forall y1 : real, (exists y2 : nat, y1 = (real_of_num y2)) -> y0 y1) = (forall y1 : nat, y0 (real_of_num y1)))) -> False) x0.
Definition term51 (x0 : nat -> Prop) := ~ (all x0).
Definition term40 (x0 : real -> Prop) := ~ (all x0).
Definition term500 (x0 : real) (x1 : real) := exists y0 : nat, ((fun y1 : nat => ~ (real_le (real_of_num y1) x1)) y0) \/ (real_le x0 x1).
Definition term243 := (~ False) -> False.
Definition term313 (x0 : real) := forall y0 : nat, (fun y1 : real => real_le y1 x0) (real_of_num y0).
Definition term161 (x0 : nat) (x1 : real -> Prop) := ((fun y0 : nat => (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x1 y1)) /\ (~ (x1 (real_of_num y0)))) x0) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))).
Definition term637 (x0 : real -> nat) (x1 : real) := exists y0 : real -> nat, (fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0.
Definition term587 (x0 : real) := exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : nat, real_le (real_of_num y2) x0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2))) y0.
Definition term560 := exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0.
Definition term256 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term840 (x0 : real -> nat) (x1 : real) := real_le (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) x1.
Definition term367 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term137 (x0 : real -> Prop) (x1 : real) (x2 : nat) := and ((fun y0 : nat => (x1 = (real_of_num y0)) /\ (~ (x0 x1))) x2).
Definition term825 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_le x0 x1))))) -> real_le x2 x3.
Definition term227 (x0 : real -> Prop) (x1 : real) := @eq Prop (~ (x0 x1)).
Definition term468 (x0 : real) := fun y0 : nat => (fun y1 : real => fun y2 : nat => ~ (real_le (real_of_num y2) y1)) x0 y0.
Definition term758 (x0 : nat) (x1 : nat) := ((real_add (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.add x0 x1))) -> False.
Definition term523 (x0 : real) := fun y0 : real => exists y1 : nat, (fun y2 : real => fun y3 : nat => (~ (real_le (real_of_num y3) y2)) \/ (real_le x0 y2)) y0 y1.
Definition term470 := fun y0 : real => exists y1 : nat, (fun y2 : real => fun y3 : nat => ~ (real_le (real_of_num y3) y2)) y0 y1.
Definition term196 (x0 : nat) (x1 : real -> Prop) := fun y0 : real => exists y1 : nat, ((forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x1 y2)) /\ (~ (x1 (real_of_num x0)))) \/ (((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))).
Definition term815 (x0 : real -> nat) (x1 : real) := Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)).
Definition term159 (x0 : real -> Prop) (x1 : nat) := or ((fun y0 : nat => (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))) x1).
Definition term452 := fun y0 : real => forall y1 : nat, ~ (real_le y0 (real_of_num y1)).
Definition term404 := fun y0 : real => forall y1 : nat, ~ (y0 = (real_of_num y1)).
Definition term208 (x0 : real) := forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0.
Definition term663 (x0 : real -> nat) (x1 : real) := exists y0 : real -> nat, exists y1 : real, (((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y0 y2)) y2)) \/ (real_le x1 y2)))) /\ (forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term376 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x0 x1) x2.
Definition term9 (x0 : Prop) := ~ (~ x0).
Definition term271 := real_of_num (NUMERAL 0).
Definition term481 := fun y0 : real -> nat => forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1).
Definition term779 (x0 : real -> nat) (x1 : real) := real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term16 (x0 : real) := fun y0 : nat => x0 = (real_of_num y0).
Definition term741 := and (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))).
Definition term719 (x0 : real) := and (forall y0 : real, forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))).
Definition term643 (x0 : real -> nat) (x1 : real) (x2 : real -> nat) := ((fun y0 : real -> nat => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) x2) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term858 (x0 : real -> nat) (x1 : real) := ~ (~ (real_le (real_of_num (x0 x1)) x1)).
Definition term548 (x0 : real) := fun y0 : real -> nat => (forall y1 : nat, real_le (real_of_num y1) x0) /\ ((fun y1 : real -> nat => forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2)) y0).
Definition term648 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term206 (x0 : real) (x1 : nat) := (fun y0 : nat => ~ (x0 = (real_of_num y0))) x1.
Definition term863 (x0 : real) := (~ (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))))) -> real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term782 (x0 : real -> nat) (x1 : real) := (~ ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))))) -> (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))).
Definition term751 (x0 : real) (x1 : nat) := (fun y0 : nat => ~ (real_le x0 (real_of_num y0))) x1.
Definition term591 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0))).
Definition term856 (x0 : real) (x1 : real -> nat) (x2 : real) := @eq Prop ((real_le x0 x2) \/ (~ (real_le (real_of_num (x1 x2)) x2))).
Definition term469 (x0 : real) := exists y0 : nat, (fun y1 : real => fun y2 : nat => ~ (real_le (real_of_num y2) y1)) x0 y0.
Definition term311 (x0 : real) := forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> real_le y0 x0.
Definition term289 (x0 : real) := ~ (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term697 (x0 : real) (x1 : real) := and (forall y0 : real, (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))).
Definition term333 (x0 : real) := and (forall y0 : real, ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) -> real_le y0 x0).
Definition term66 (x0 : real -> Prop) := and (forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)).
Definition term65 (x0 : real -> Prop) := and (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0).
Definition term209 (x0 : real) := or (forall y0 : nat, (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0).
Definition term89 (x0 : real -> Prop) := or (exists y0 : nat, (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))).
Definition term822 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x1 x2)).
Definition term830 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_le x1 x2))).
Definition term800 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term831 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term641 (x0 : real -> nat) (x1 : real) (x2 : real -> nat) := and ((fun y0 : real -> nat => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) x2).
Definition term224 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ~ (x0 y0)) x1.
Definition term384 (x0 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term731 (x0 : real) := and ((fun y0 : real => forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) x0).
Definition term28 (x0 : real) (x1 : nat) := ~ (x0 = (real_of_num x1)).
Definition term217 (x0 : real -> Prop) (x1 : real) := fun y0 : nat => (~ (x1 = (real_of_num y0))) \/ (x0 x1).
Definition term753 (x0 : real) := (fun y0 : real => ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term323 (x0 : real) := fun y0 : nat => real_le (real_of_num y0) x0.
Definition term369 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)).
Definition term390 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term816 (x0 : real -> nat) (x1 : real) := (~ (real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1)) -> real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1.
Definition term768 (x0 : real -> nat) (x1 : real) := (~ (real_le (real_of_num (x0 x1)) x1)) -> real_le (real_of_num (x0 x1)) x1.
Definition term393 := fun y0 : real => ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term291 := (fun y0 : real -> Prop => ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) (fun y0 : real => exists y1 : nat, y0 = (real_of_num y1)).
Definition term48 (x0 : real -> Prop) := exists y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) /\ (~ (x0 y0)).
Definition term846 (x0 : real) (x1 : real) (x2 : real) := imp (~ (~ (real_le (real_add x0 x1) x2))).
Definition term240 (x0 : real -> Prop) (x1 : nat) := ((real_of_num x1) = (real_of_num x1)) -> x0 (real_of_num x1).
Definition term589 (x0 : real -> nat) (x1 : real) := @eq Prop (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real -> nat, (forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))).
Definition term588 (x0 : real -> nat) (x1 : real) := @eq Prop (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2))) y0)).
Definition term577 (x0 : real -> nat) := @eq Prop (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))).
Definition term576 (x0 : real -> nat) := @eq Prop (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real, (fun y1 : real => exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))) y0)).
Definition term53 (x0 : real -> Prop) := ~ (forall y0 : nat, x0 (real_of_num y0)).
Definition term228 (x0 : nat) := (~ ((real_of_num x0) = (real_of_num x0))) -> (real_of_num x0) = (real_of_num x0).
Definition term453 := exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)).
Definition term328 := exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0.
Definition term327 := exists y0 : real, forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0.
Definition term740 := and (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0).
Definition term718 (x0 : real) := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0).
Definition term696 (x0 : real) (x1 : real) := and (forall y0 : real, (fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0).
Definition term74 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term805 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term42 (x0 : real -> Prop) := ~ (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0).
Definition term266 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term231 (x0 : real -> Prop) (x1 : real) (x2 : nat) := (x0 x1) \/ (~ (x1 = (real_of_num x2))).
Definition term841 (x0 : real -> nat) (x1 : real) := (~ (real_le (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) x1)) -> real_le (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) x1.
Definition term2 (x0 : real -> Prop) := forall y0 : nat, x0 (real_of_num y0).
Definition term309 (x0 : real) := fun y0 : real => (exists y1 : nat, y0 = (real_of_num y1)) -> real_le y0 x0.
Definition term84 (x0 : real -> Prop) (x1 : nat) := (forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ ((fun y0 : nat => ~ (x0 (real_of_num y0))) x1).
Definition term382 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term845 (x0 : real) (x1 : real) (x2 : real) := ~ (~ (real_le (real_add x0 x1) x2)).
Definition term838 (x0 : real -> nat) (x1 : real) := ((real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0))))) /\ ((x1 = x1) /\ (real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1)).
Definition term581 (x0 : real -> nat) := fun y0 : real => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ (exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term702 (x0 : real) := fun y0 : real => (forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) /\ (forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)).
Definition term433 := fun y0 : real => (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (exists y2 : nat, ~ (real_le (real_of_num y2) y1)) \/ (real_le y0 y1)).
Definition term346 := fun y0 : real => (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1).
Definition term345 := fun y0 : real => (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => exists y4 : nat, y3 = (real_of_num y4)) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term541 (x0 : real) (x1 : real -> nat) := (fun y0 : real -> nat => forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1)) x1.
Definition term594 (x0 : real -> nat) (x1 : real) := exists y0 : real -> nat, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1))).
Definition term113 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term388 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term546 (x0 : real) (x1 : real -> nat) := (forall y0 : nat, real_le (real_of_num y0) x0) /\ ((fun y0 : real -> nat => forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1)) x1).
Definition term26 (x0 : real) (x1 : nat) := (fun y0 : nat => x0 = (real_of_num y0)) x1.
Definition term170 (x0 : nat) (x1 : real -> Prop) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x1 y0)) /\ (~ (x1 (real_of_num x0)))) \/ (exists y0 : real, (fun y1 : real => exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x1 y1))) /\ (forall y3 : nat, x1 (real_of_num y3))) y0).
Definition term537 (x0 : Prop) (x1 : type1024) := x0 /\ (exists y0 : real -> nat, x1 y0).
Definition term235 (x0 : nat) (x1 : real -> Prop) (x2 : real) := (~ (~ (x2 = (real_of_num x0)))) -> x1 x2.
Definition term183 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term745 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)).
Definition term723 (x0 : real) := (forall y0 : real, forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) /\ (forall y0 : real, forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)).
Definition term130 (x0 : real) (x1 : real -> Prop) := exists y0 : nat, ((fun y1 : nat => (x0 = (real_of_num y1)) /\ (~ (x1 x0))) y0) /\ (forall y1 : nat, x1 (real_of_num y1)).
Definition term45 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) x1).
Definition term542 (x0 : real) := fun y0 : real -> nat => (fun y1 : real -> nat => forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2)) y0.
Definition term489 := fun y0 : real -> nat => (fun y1 : real -> nat => forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2)) y0.
Definition term466 (x0 : real) (x1 : nat) := (fun y0 : real => fun y1 : nat => ~ (real_le (real_of_num y1) y0)) x0 x1.
Definition term248 (x0 : real) := real_sub x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term234 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term100 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : nat, x1 = (real_of_num y0)) /\ (~ (x0 x1))).
Definition term99 (x0 : real -> Prop) (x1 : real) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x1 = (real_of_num y1)) y0) /\ (~ (x0 x1))).
Definition term129 (x0 : real) (x1 : real -> Prop) := (exists y0 : nat, (fun y1 : nat => (x0 = (real_of_num y1)) /\ (~ (x1 x0))) y0) /\ (forall y0 : nat, x1 (real_of_num y0)).
Definition term114 (x0 : real -> Prop) := (exists y0 : real, (fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0) /\ (forall y0 : nat, x0 (real_of_num y0)).
Definition term336 (x0 : real) := imp (forall y0 : nat, real_le (real_of_num y0) x0).
Definition term483 := (forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (exists y0 : real -> nat, forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1)).
Definition term727 := (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (~ (real_le y1 (real_sub y2 y3))) \/ (real_le (real_add y1 y3) y2)) y0).
Definition term705 (x0 : real) := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le x0 (real_sub y1 y2))) \/ (real_le (real_add x0 y2) y1)) y0).
Definition term680 (x0 : real) (x1 : real) := (forall y0 : real, (fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_le x0 (real_sub x1 y1))) \/ (real_le (real_add x0 y1) x1)) y0).
Definition term474 (x0 : real -> nat) (x1 : real) := (fun y0 : nat => ~ (real_le (real_of_num y0) x1)) (x0 x1).
Definition term190 (x0 : nat) (x1 : real) (x2 : real -> Prop) := @eq Prop (((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x2 y0)) /\ (~ (x2 (real_of_num x0)))) \/ (exists y0 : nat, ((x1 = (real_of_num y0)) /\ (~ (x2 x1))) /\ (forall y1 : nat, x2 (real_of_num y1)))).
Definition term189 (x0 : nat) (x1 : real) (x2 : real -> Prop) := @eq Prop (((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x2 y0)) /\ (~ (x2 (real_of_num x0)))) \/ (exists y0 : nat, (fun y1 : nat => ((x1 = (real_of_num y1)) /\ (~ (x2 x1))) /\ (forall y2 : nat, x2 (real_of_num y2))) y0)).
Definition term176 (x0 : nat) (x1 : real -> Prop) := @eq Prop (((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x1 y0)) /\ (~ (x1 (real_of_num x0)))) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2)))).
Definition term175 (x0 : nat) (x1 : real -> Prop) := @eq Prop (((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x1 y0)) /\ (~ (x1 (real_of_num x0)))) \/ (exists y0 : real, (fun y1 : real => exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x1 y1))) /\ (forall y3 : nat, x1 (real_of_num y3))) y0)).
Definition term550 (x0 : real) := exists y0 : real -> nat, (forall y1 : nat, real_le (real_of_num y1) x0) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1)).
Definition term57 (x0 : real -> Prop) (x1 : nat) := ~ (x0 (real_of_num x1)).
Definition term105 (x0 : real -> Prop) (x1 : real) := fun y0 : nat => ((fun y1 : nat => x1 = (real_of_num y1)) y0) /\ (~ (x0 x1)).
Definition term211 (x0 : real -> Prop) (x1 : real) := @eq Prop ((forall y0 : nat, ~ (x1 = (real_of_num y0))) \/ (x0 x1)).
Definition term210 (x0 : real -> Prop) (x1 : real) := @eq Prop ((forall y0 : nat, (fun y1 : nat => ~ (x1 = (real_of_num y1))) y0) \/ (x0 x1)).
Definition term554 (x0 : type1024) (x1 : Prop) := (exists y0 : real -> nat, x0 y0) \/ x1.
Definition term149 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) \/ x1.
Definition term766 (x0 : real -> nat) (x1 : real) := real_of_num (x0 x1).
Definition term667 := exists y0 : real -> nat, exists y1 : real, exists y2 : real -> nat, exists y3 : real, (((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y0 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y1) /\ (forall y4 : real, (~ (real_le (real_of_num (y2 y4)) y4)) \/ (real_le y1 y4)))) /\ (forall y4 : nat, ~ (real_le y3 (real_of_num y4))).
Definition term598 := exists y0 : real -> nat, exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))).
Definition term73 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term495 := fun y0 : real -> nat => (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ ((fun y1 : real -> nat => forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2)) y0).
Definition term49 (x0 : real -> Prop) := fun y0 : real => (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0).
Definition term666 := fun y0 : real -> nat => exists y1 : real, exists y2 : real -> nat, exists y3 : real, (((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y0 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y1) /\ (forall y4 : real, (~ (real_le (real_of_num (y2 y4)) y4)) \/ (real_le y1 y4)))) /\ (forall y4 : nat, ~ (real_le y3 (real_of_num y4))).
Definition term597 := fun y0 : real -> nat => exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))).
Definition term812 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term260 (x0 : real) := real_add x0 (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term520 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (~ (real_le (real_of_num y0) x1)) \/ (real_le x0 x1)) x2.
Definition term59 (x0 : real -> Prop) := fun y0 : nat => ~ (x0 (real_of_num y0)).
Definition term536 (x0 : real) := (forall y0 : nat, real_le (real_of_num y0) x0) /\ (exists y0 : real -> nat, forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1)).
Definition term230 (x0 : Prop) := (~ x0) -> x0.
Definition term556 := (exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term151 (x0 : real -> Prop) := (exists y0 : nat, (fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2))).
Definition term254 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term141 (x0 : real) (x1 : real -> Prop) := fun y0 : nat => ((fun y1 : nat => (x0 = (real_of_num y1)) /\ (~ (x1 x0))) y0) /\ (forall y1 : nat, x1 (real_of_num y1)).
Definition term568 := fun y0 : real -> nat => ((fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0) \/ (exists y1 : real, exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))).
Definition term521 (x0 : real) (x1 : real) := fun y0 : nat => (fun y1 : real => fun y2 : nat => (~ (real_le (real_of_num y2) y1)) \/ (real_le x0 y1)) x1 y0.
Definition term195 (x0 : nat) (x1 : real) (x2 : real -> Prop) := exists y0 : nat, ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x2 y1)) /\ (~ (x2 (real_of_num x0)))) \/ (((x1 = (real_of_num y0)) /\ (~ (x2 x1))) /\ (forall y1 : nat, x2 (real_of_num y1))).
Definition term485 (x0 : Prop) (x1 : type1024) := exists y0 : real -> nat, x0 \/ (x1 y0).
Definition term286 := and ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term247 (x0 : real) := real_ge (real_sub (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term796 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term742 := fun y0 : real => (fun y1 : real => forall y2 : real, forall y3 : real, (~ (real_le y1 (real_sub y2 y3))) \/ (real_le (real_add y1 y3) y2)) y0.
Definition term737 := fun y0 : real => (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0.
Definition term720 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_le x0 (real_sub y1 y2))) \/ (real_le (real_add x0 y2) y1)) y0.
Definition term715 (x0 : real) := fun y0 : real => (fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0.
Definition term653 := fun y0 : real => (fun y1 : real => forall y2 : nat, ~ (real_le y1 (real_of_num y2))) y0.
Definition term658 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) (x3 : real) := (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))) /\ (forall y0 : nat, ~ (real_le x3 (real_of_num y0))).
Definition term849 (x0 : real -> nat) (x1 : real) := (real_le (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) x1) -> real_le (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term431 (x0 : real) := forall y0 : real, (exists y1 : nat, ~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0).
Definition term798 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term457 := (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0))) \/ (exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (exists y2 : nat, ~ (real_le (real_of_num y2) y1)) \/ (real_le y0 y1)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term482 := exists y0 : real -> nat, forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1).
Definition term458 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term476 (x0 : real -> nat) := fun y0 : real => (fun y1 : real => fun y2 : nat => ~ (real_le (real_of_num y2) y1)) y0 (x0 y0).
Definition term861 (x0 : real -> nat) (x1 : real) (x2 : real) := (real_le (real_of_num (x0 x2)) x2) -> real_le x1 x2.
Definition term605 (x0 : real -> nat) := (fun y0 : real -> nat => exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) x0.
Definition term793 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term595 (x0 : real -> nat) := fun y0 : real => exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term71 (x0 : real -> Prop) := ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) /\ (~ (forall y0 : nat, x0 (real_of_num y0)))) \/ ((~ (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0)) /\ (forall y0 : nat, x0 (real_of_num y0))).
Definition term134 (x0 : real -> Prop) (x1 : real) := and (exists y0 : nat, (fun y1 : nat => (x1 = (real_of_num y1)) /\ (~ (x0 x1))) y0).
Definition term98 (x0 : real) := and (exists y0 : nat, (fun y1 : nat => x0 = (real_of_num y1)) y0).
Definition term669 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) /\ ((~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1)).
Definition term368 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term744 := forall y0 : real, forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1).
Definition term739 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1)).
Definition term722 (x0 : real) := forall y0 : real, forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0).
Definition term717 (x0 : real) := forall y0 : real, forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0)).
Definition term674 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) /\ ((~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)).
Definition term672 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) /\ ((~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)).
Definition term405 := forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1)).
Definition term392 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term380 (x0 : real) := forall y0 : real, forall y1 : real, (real_le x0 (real_sub y0 y1)) = (real_le (real_add x0 y1) y0).
Definition term363 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1).
Definition term220 (x0 : real -> Prop) := forall y0 : real, forall y1 : nat, (~ (y0 = (real_of_num y1))) \/ (x0 y0).
Definition term408 (x0 : real) (x1 : nat) := (fun y0 : nat => real_le (real_of_num y0) x0) x1.
Definition term426 (x0 : real) := or (~ (forall y0 : nat, real_le (real_of_num y0) x0)).
Definition term18 (x0 : real) := imp (exists y0 : nat, x0 = (real_of_num y0)).
Definition term553 := (exists y0 : real -> nat, (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term146 (x0 : real -> Prop) := (exists y0 : nat, (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2))).
Definition term794 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term535 (x0 : real) := exists y0 : real -> nat, forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1).
Definition term516 (x0 : real) := exists y0 : real -> nat, forall y1 : real, (fun y2 : real => fun y3 : nat => (~ (real_le (real_of_num y3) y2)) \/ (real_le x0 y2)) y1 (y0 y1).
Definition term463 := exists y0 : real -> nat, forall y1 : real, (fun y2 : real => fun y3 : nat => ~ (real_le (real_of_num y3) y2)) y1 (y0 y1).
Definition term461 (x0 : type1622) := exists y0 : real -> nat, forall y1 : real, x0 y1 (y0 y1).
Definition term670 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) /\ ((~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1)).
Definition term665 (x0 : real -> nat) := exists y0 : real, exists y1 : real -> nat, exists y2 : real, (((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y0) /\ (forall y3 : real, (~ (real_le (real_of_num (y1 y3)) y3)) \/ (real_le y0 y3)))) /\ (forall y3 : nat, ~ (real_le y2 (real_of_num y3))).
Definition term596 (x0 : real -> nat) := exists y0 : real, exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term552 := exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)).
Definition term302 := exists y0 : real, exists y1 : nat, y0 = (real_of_num y1).
Definition term197 (x0 : nat) (x1 : real -> Prop) := exists y0 : real, exists y1 : nat, ((forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x1 y2)) /\ (~ (x1 (real_of_num x0)))) \/ (((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))).
Definition term145 (x0 : real -> Prop) := exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2)).
Definition term109 (x0 : real -> Prop) := exists y0 : real, exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0)).
Definition term399 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term493 (x0 : real -> nat) := (forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ ((fun y0 : real -> nat => forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1)) x0).
Definition term850 (x0 : real -> nat) (x1 : real) := real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term107 (x0 : real -> Prop) (x1 : real) := exists y0 : nat, (x1 = (real_of_num y0)) /\ (~ (x0 x1)).
Definition term60 (x0 : real -> Prop) := exists y0 : nat, ~ (x0 (real_of_num y0)).
Definition term465 (x0 : real) := (fun y0 : real => fun y1 : nat => ~ (real_le (real_of_num y1) y0)) x0.
Definition term676 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term214 (x0 : nat) (x1 : real -> Prop) (x2 : real) := ((fun y0 : nat => ~ (x2 = (real_of_num y0))) x0) \/ (x1 x2).
Definition term365 := (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term374 := (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)).
Definition term438 := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0))) \/ (exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (exists y2 : nat, ~ (real_le (real_of_num y2) y1)) \/ (real_le y0 y1))).
Definition term590 (x0 : real -> nat) (x1 : real) (x2 : real -> nat) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((fun y0 : real -> nat => (forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1))) x2).
Definition term649 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term203 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) \/ x1.
Definition term200 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term177 (x0 : nat) (x1 : real -> Prop) (x2 : real) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x1 y0)) /\ (~ (x1 (real_of_num x0)))) \/ ((fun y0 : real => exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))) x2).
Definition term528 (x0 : real -> nat) (x1 : real) (x2 : real) := (~ (real_le (real_of_num (x0 x2)) x2)) \/ (real_le x1 x2).
Definition term509 (x0 : nat) (x1 : real) (x2 : real) := (~ (real_le (real_of_num x0) x2)) \/ (real_le x1 x2).
Definition term617 := exists y0 : real -> nat, (exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term115 (x0 : real -> Prop) := exists y0 : real, ((fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0) /\ (forall y1 : nat, x0 (real_of_num y1)).
Definition term34 (x0 : real -> Prop) (x1 : real) := (exists y0 : nat, x1 = (real_of_num y0)) /\ (~ (x0 x1)).
Definition term162 (x0 : nat) (x1 : real -> Prop) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x1 y0)) /\ (~ (x1 (real_of_num x0)))) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))).
Definition term529 (x0 : real) (x1 : real -> nat) := fun y0 : real => (fun y1 : real => fun y2 : nat => (~ (real_le (real_of_num y2) y1)) \/ (real_le x0 y1)) y0 (x1 y0).
Definition term791 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term265 (x0 : real) := real_add (real_add x0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term646 (x0 : real -> nat) (x1 : real) := fun y0 : real -> nat => (((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term767 (x0 : real -> nat) (x1 : real) := real_le (real_of_num (x0 x1)) x1.
Definition term473 (x0 : real -> nat) (x1 : real) := (fun y0 : real => fun y1 : nat => ~ (real_le (real_of_num y1) y0)) x1 (x0 x1).
Definition term409 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => real_le (real_of_num y0) x0) x1).
Definition term566 (x0 : real -> nat) := ((fun y0 : real -> nat => (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) x0) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term747 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term538 (x0 : Prop) (x1 : type1024) := exists y0 : real -> nat, x0 /\ (x1 y0).
Definition term290 := forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term283 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term124 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real => exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x1 y0))) x0) /\ (forall y0 : nat, x1 (real_of_num y0)).
Definition term104 (x0 : nat) (x1 : real -> Prop) (x2 : real) := (x2 = (real_of_num x0)) /\ (~ (x1 x2)).
Definition term505 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : nat, ~ (real_le (real_of_num y0) x1)) \/ (real_le x0 x1)).
Definition term504 (x0 : real) (x1 : real) := @eq Prop ((exists y0 : nat, (fun y1 : nat => ~ (real_le (real_of_num y1) x1)) y0) \/ (real_le x0 x1)).
Definition term35 (x0 : real -> Prop) (x1 : real) := ~ ((exists y0 : nat, x1 = (real_of_num y0)) -> x0 x1).
Definition term448 := exists y0 : real, ~ ((fun y1 : real => exists y2 : nat, real_le y1 (real_of_num y2)) y0).
Definition term43 (x0 : real -> Prop) := exists y0 : real, ~ ((fun y1 : real => (exists y2 : nat, y1 = (real_of_num y2)) -> x0 y1) y0).
Definition term68 (x0 : real -> Prop) := (forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (exists y0 : nat, ~ (x0 (real_of_num y0))).
Definition term569 := fun y0 : real -> nat => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) \/ (exists y1 : real, exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))).
Definition term288 (x0 : real) := ((~ (~ (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0))))))) -> False) -> ~ (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term449 (x0 : real) := (fun y0 : real => exists y1 : nat, real_le y0 (real_of_num y1)) x0.
Definition term297 (x0 : real) := (fun y0 : real => exists y1 : nat, y0 = (real_of_num y1)) x0.
Definition term567 (x0 : real -> nat) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term245 (x0 : real) := ~ (~ (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term835 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3))).
Definition term282 (x0 : nat) (x1 : nat) := real_ge (real_neg (real_of_num x0)) (real_of_num x1).
Definition term586 (x0 : real) := fun y0 : real -> nat => (fun y1 : real -> nat => (forall y2 : nat, real_le (real_of_num y2) x0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2))) y0.
Definition term559 := fun y0 : real -> nat => (fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0.
Definition term484 (x0 : Prop) (x1 : type1024) := x0 \/ (exists y0 : real -> nat, x1 y0).
Definition term180 (x0 : nat) (x1 : real -> Prop) := fun y0 : real => ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x1 y1)) /\ (~ (x1 (real_of_num x0)))) \/ (exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))).
Definition term300 (x0 : real) := @eq Prop ((fun y0 : real => exists y1 : nat, y0 = (real_of_num y1)) x0).
Definition term320 (x0 : real) (x1 : nat) := (fun y0 : real => real_le y0 x0) (real_of_num x1).
Definition term414 := ~ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0).
Definition term400 := ~ (exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)).
Definition term526 (x0 : real) (x1 : real -> nat) (x2 : real) := (fun y0 : real => fun y1 : nat => (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0)) x2 (x1 x2).
Definition term446 (x0 : real) := forall y0 : nat, ~ (real_le x0 (real_of_num y0)).
Definition term31 (x0 : real) := forall y0 : nat, ~ (x0 = (real_of_num y0)).
Definition term512 (x0 : real) (x1 : real) := exists y0 : nat, (~ (real_le (real_of_num y0) x1)) \/ (real_le x0 x1).
Definition term198 (x0 : real -> Prop) := fun y0 : nat => exists y1 : real, exists y2 : nat, ((forall y3 : real, (forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (x0 y3)) /\ (~ (x0 (real_of_num y0)))) \/ (((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))).
Definition term611 (x0 : real -> nat) := and ((fun y0 : real -> nat => exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) x0).
Definition term502 (x0 : real) := exists y0 : nat, (fun y1 : nat => ~ (real_le (real_of_num y1) x0)) y0.
Definition term81 (x0 : real -> Prop) := exists y0 : nat, (fun y1 : nat => ~ (x0 (real_of_num y1))) y0.
Definition term451 := fun y0 : real => ~ ((fun y1 : real => exists y2 : nat, real_le y1 (real_of_num y2)) y0).
Definition term418 := fun y0 : real => ~ ((fun y1 : real => forall y2 : nat, real_le (real_of_num y2) y1) y0).
Definition term403 := fun y0 : real => ~ ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0).
Definition term76 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term427 (x0 : real) := or (exists y0 : nat, ~ (real_le (real_of_num y0) x0)).
Definition term572 (x0 : real -> nat) := exists y0 : real, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((fun y1 : real => exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))) y0).
Definition term171 (x0 : nat) (x1 : real -> Prop) := exists y0 : real, ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x1 y1)) /\ (~ (x1 (real_of_num x0)))) \/ ((fun y1 : real => exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x1 y1))) /\ (forall y3 : nat, x1 (real_of_num y3))) y0).
Definition term736 := @eq Prop (forall y0 : real, (forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) /\ (forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1))).
Definition term735 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, (~ (real_le y1 (real_sub y2 y3))) \/ (real_le (real_add y1 y3) y2)) y0)).
Definition term714 (x0 : real) := @eq Prop (forall y0 : real, (forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) /\ (forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0))).
Definition term713 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_le x0 (real_sub y1 y2))) \/ (real_le (real_add x0 y2) y1)) y0)).
Definition term692 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) /\ ((~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1))).
Definition term691 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0) /\ ((fun y1 : real => (~ (real_le x0 (real_sub x1 y1))) \/ (real_le (real_add x0 y1) x1)) y0)).
Definition term319 (x0 : real) := @eq Prop (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> real_le y0 x0).
Definition term318 (x0 : real) := @eq Prop (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> (fun y1 : real => real_le y1 x0) y0).
Definition term21 (x0 : real -> Prop) := @eq Prop (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0).
Definition term862 (x0 : real -> nat) (x1 : real) := (real_le (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) -> real_le x1 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term681 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1)).
Definition term186 (x0 : real) (x1 : real -> Prop) (x2 : nat) := (fun y0 : nat => ((x0 = (real_of_num y0)) /\ (~ (x1 x0))) /\ (forall y1 : nat, x1 (real_of_num y1))) x2.
Definition term684 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 (real_sub x2 x1)) \/ (~ (real_le (real_add x0 x1) x2)).
Definition term778 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term412 (x0 : real) := fun y0 : nat => ~ (real_le (real_of_num y0) x0).
Definition term340 (x0 : real) := fun y0 : real => (forall y1 : nat, real_le (real_of_num y1) y0) -> real_le x0 y0.
Definition term339 (x0 : real) := fun y0 : real => (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) -> real_le x0 y0.
Definition term756 (x0 : nat) (x1 : nat) := ~ ((real_add (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.add x0 x1))).
Definition term88 (x0 : real -> Prop) := exists y0 : nat, (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0))).
Definition term38 (x0 : real -> Prop) (x1 : real) := (~ (exists y0 : nat, x1 = (real_of_num y0))) \/ (x0 x1).
Definition term817 (x0 : real -> nat) (x1 : real) := ~ (real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1).
Definition term475 (x0 : real -> nat) (x1 : real) := ~ (real_le (real_of_num (x0 x1)) x1).
Definition term564 (x0 : real -> nat) := or ((fun y0 : real -> nat => (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) x0).
Definition term75 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term191 (x0 : nat) (x1 : real) (x2 : real -> Prop) (x3 : nat) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x2 y0)) /\ (~ (x2 (real_of_num x0)))) \/ ((fun y0 : nat => ((x1 = (real_of_num y0)) /\ (~ (x2 x1))) /\ (forall y1 : nat, x2 (real_of_num y1))) x3).
Definition term671 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) /\ ((~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)).
Definition term640 (x0 : real -> nat) (x1 : real) := @eq Prop ((exists y0 : real -> nat, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term639 (x0 : real -> nat) (x1 : real) := @eq Prop ((exists y0 : real -> nat, (fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term625 (x0 : real -> nat) := @eq Prop ((exists y0 : real, exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term624 (x0 : real -> nat) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term610 := @eq Prop ((exists y0 : real -> nat, exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term609 := @eq Prop ((exists y0 : real -> nat, (fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term478 (x0 : real -> nat) := forall y0 : real, (fun y1 : real => fun y2 : nat => ~ (real_le (real_of_num y2) y1)) y0 (x0 y0).
Definition term497 := exists y0 : real -> nat, (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1)).
Definition term139 (x0 : real) (x1 : nat) (x2 : real -> Prop) := ((fun y0 : nat => (x0 = (real_of_num y0)) /\ (~ (x2 x0))) x1) /\ (forall y0 : nat, x2 (real_of_num y0)).
Definition term361 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term518 (x0 : real) (x1 : real) := (fun y0 : real => fun y1 : nat => (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0)) x1.
Definition term776 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term213 (x0 : real) (x1 : nat) := or (~ (x0 = (real_of_num x1))).
Definition term13 := forall y0 : real -> Prop, (forall y1 : real, (exists y2 : nat, y1 = (real_of_num y2)) -> y0 y1) = (forall y1 : nat, y0 (real_of_num y1)).
Definition term270 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term257 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term87 (x0 : real -> Prop) := fun y0 : nat => (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0))).
Definition term17 (x0 : real) := exists y0 : nat, x0 = (real_of_num y0).
Definition term783 (x0 : real -> nat) (x1 : real) := ~ ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0))))).
Definition term154 (x0 : real -> Prop) := fun y0 : nat => (fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0.
Definition term132 (x0 : real -> Prop) (x1 : real) := fun y0 : nat => (fun y1 : nat => (x1 = (real_of_num y1)) /\ (~ (x0 x1))) y0.
Definition term629 (x0 : real -> nat) (x1 : real) := (exists y0 : real -> nat, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term233 (x0 : real -> Prop) (x1 : real) (x2 : nat) := @eq Prop ((x0 x1) \/ (~ (x1 = (real_of_num x2)))).
Definition term63 (x0 : real -> Prop) := (~ (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0)) /\ (forall y0 : nat, x0 (real_of_num y0)).
Definition term95 (x0 : real -> Prop) (x1 : real) := exists y0 : nat, ((fun y1 : nat => x1 = (real_of_num y1)) y0) /\ (~ (x0 x1)).
Definition term857 (x0 : real -> nat) (x1 : real) (x2 : real) := (~ (~ (real_le (real_of_num (x0 x2)) x2))) -> real_le x1 x2.
Definition term607 := exists y0 : real -> nat, (fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0.
Definition term543 (x0 : real) := exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2)) y0.
Definition term490 := exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2)) y0.
Definition term70 (x0 : real -> Prop) := or ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (exists y0 : nat, ~ (x0 (real_of_num y0)))).
Definition term788 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term820 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term232 (x0 : nat) (x1 : real -> Prop) (x2 : real) := @eq Prop ((~ (x2 = (real_of_num x0))) \/ (x1 x2)).
Definition term760 (x0 : real -> nat) (x1 : real) := (real_le x1 (real_of_num (x0 x1))) -> ~ (real_le x1 (real_of_num (x0 x1))).
Definition term360 := (((~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False) -> (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False) -> ((~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False) -> (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term338 (x0 : real) (x1 : real) := (forall y0 : nat, real_le (real_of_num y0) x1) -> real_le x0 x1.
Definition term337 (x0 : real) (x1 : real) := (forall y0 : real, ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) -> real_le y0 x1) -> real_le x0 x1.
Definition term447 := ~ (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term362 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)).
Definition term769 (x0 : real -> nat) (x1 : real) := (real_le (real_of_num (x0 x1)) x1) -> False.
Definition term419 := fun y0 : real => exists y1 : nat, ~ (real_le (real_of_num y1) y0).
Definition term342 (x0 : real) := forall y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) -> real_le x0 y0.
Definition term341 (x0 : real) := forall y0 : real, (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) -> real_le x0 y0.
Definition term688 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 (real_sub x2 x1))) \/ (real_le (real_add x0 x1) x2).
Definition term422 := or (forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))).
Definition term510 (x0 : real) (x1 : real) := fun y0 : nat => ((fun y1 : nat => ~ (real_le (real_of_num y1) x1)) y0) \/ (real_le x0 x1).
Definition term314 (x0 : real) := fun y0 : real => real_le y0 x0.
Definition term138 (x0 : nat) (x1 : real -> Prop) (x2 : real) := and ((x2 = (real_of_num x0)) /\ (~ (x1 x2))).
Definition term142 (x0 : real) (x1 : real -> Prop) := fun y0 : nat => ((x0 = (real_of_num y0)) /\ (~ (x1 x0))) /\ (forall y1 : nat, x1 (real_of_num y1)).
Definition term775 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term307 (x0 : real) (x1 : real) := (exists y0 : nat, x0 = (real_of_num y0)) -> real_le x0 x1.
Definition term687 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1)) x2.
Definition term5 (x0 : real -> Prop) := ((~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False) -> (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False.
Definition term771 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le x2 x3) = (real_le x0 x1)) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term525 (x0 : real) := @eq Prop (forall y0 : real, exists y1 : nat, (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0)).
Definition term524 (x0 : real) := @eq Prop (forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => (~ (real_le (real_of_num y3) y2)) \/ (real_le x0 y2)) y0 y1).
Definition term472 := @eq Prop (forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0)).
Definition term471 := @eq Prop (forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => ~ (real_le (real_of_num y3) y2)) y0 y1).
Definition term711 (x0 : real) (x1 : real) := ((fun y0 : real => forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) x1) /\ ((fun y0 : real => forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)) x1).
Definition term486 := (forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2)) y0).
Definition term824 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term754 (x0 : real -> nat) (x1 : real) (x2 : real) := (fun y0 : real => (~ (real_le (real_of_num (x0 y0)) y0)) \/ (real_le x1 y0)) x2.
Definition term140 (x0 : nat) (x1 : real) (x2 : real -> Prop) := ((x1 = (real_of_num x0)) /\ (~ (x2 x1))) /\ (forall y0 : nat, x2 (real_of_num y0)).
Definition term787 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term582 (x0 : real -> nat) := exists y0 : real, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ (exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))).
Definition term181 (x0 : nat) (x1 : real -> Prop) := exists y0 : real, ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x1 y1)) /\ (~ (x1 (real_of_num x0)))) \/ (exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x1 y0))) /\ (forall y2 : nat, x1 (real_of_num y2))).
Definition term621 (x0 : real -> nat) := fun y0 : real => (fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0.
Definition term574 := fun y0 : real => (fun y1 : real => exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))) y0.
Definition term298 := fun y0 : real => (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0.
Definition term173 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))) y0.
Definition term117 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0.
Definition term167 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term860 (x0 : real -> nat) (x1 : real) := imp (real_le (real_of_num (x0 x1)) x1).
Definition term818 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term864 (x0 : real) := (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0))))) -> False.
Definition term294 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term635 (x0 : real -> nat) (x1 : real) (x2 : real -> nat) := (fun y0 : real -> nat => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) x2.
Definition term814 (x0 : real -> nat) (x1 : real) := real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1.
Definition term477 (x0 : real -> nat) := fun y0 : real => ~ (real_le (real_of_num (x0 y0)) y0).
Definition term263 (x0 : real) := real_sub (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term334 (x0 : real) := and (forall y0 : nat, real_le (real_of_num y0) x0).
Definition term645 (x0 : real -> nat) (x1 : real) := fun y0 : real -> nat => ((fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term615 := fun y0 : real -> nat => ((fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term797 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term492 := @eq Prop ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (exists y0 : real -> nat, forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))).
Definition term491 := @eq Prop ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2)) y0)).
Definition term349 := ((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1).
Definition term293 := ((exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => exists y4 : nat, y3 = (real_of_num y4)) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term321 (x0 : nat) (x1 : real) := real_le (real_of_num x0) x1.
Definition term701 (x0 : real) (x1 : real) := (forall y0 : real, (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) /\ (forall y0 : real, (~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1)).
Definition term343 (x0 : real) := (forall y0 : real, ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) -> real_le y0 x0) /\ (forall y0 : real, (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) -> real_le x0 y0).
Definition term539 (x0 : real) := (forall y0 : nat, real_le (real_of_num y0) x0) /\ (exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2)) y0).
Definition term387 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term11 := fun y0 : real -> Prop => (forall y1 : real, (exists y2 : nat, y1 = (real_of_num y2)) -> y0 y1) = (forall y1 : nat, y0 (real_of_num y1)).
Definition term761 (x0 : real -> nat) (x1 : real) := real_le x1 (real_of_num (x0 x1)).
Definition term332 := imp ((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)).
Definition term331 := imp ((exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0)).
Definition term166 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term551 := fun y0 : real => exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)).
Definition term72 (x0 : real -> Prop) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (exists y0 : nat, ~ (x0 (real_of_num y0)))) \/ ((exists y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y0 : nat, x0 (real_of_num y0))).
Definition term276 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term614 (x0 : real -> nat) := (exists y0 : real, exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term600 := (exists y0 : real -> nat, exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term330 := (exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0).
Definition term506 (x0 : real) (x1 : nat) := or ((fun y0 : nat => ~ (real_le (real_of_num y0) x0)) x1).
Definition term212 (x0 : real) (x1 : nat) := or ((fun y0 : nat => ~ (x0 = (real_of_num y0))) x1).
Definition term237 (x0 : real) (x1 : nat) := imp (~ (~ (x0 = (real_of_num x1)))).
Definition term488 (x0 : real -> nat) := (fun y0 : real -> nat => forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1)) x0.
Definition term638 (x0 : real -> nat) (x1 : real) := and (exists y0 : real -> nat, (fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0).
Definition term608 := and (exists y0 : real -> nat, (fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0).
Definition term185 (x0 : nat) (x1 : real) (x2 : real -> Prop) := exists y0 : nat, ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x2 y1)) /\ (~ (x2 (real_of_num x0)))) \/ ((fun y1 : nat => ((x1 = (real_of_num y1)) /\ (~ (x2 x1))) /\ (forall y2 : nat, x2 (real_of_num y2))) y0).
Definition term246 (x0 : real) := real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term202 (x0 : nat -> Prop) (x1 : Prop) := (forall y0 : nat, x0 y0) \/ x1.
Definition term450 (x0 : real) := ~ ((fun y0 : real => exists y1 : nat, real_le y0 (real_of_num y1)) x0).
Definition term417 (x0 : real) := ~ ((fun y0 : real => forall y1 : nat, real_le (real_of_num y1) y0) x0).
Definition term402 (x0 : real) := ~ ((fun y0 : real => exists y1 : nat, y0 = (real_of_num y1)) x0).
Definition term251 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term398 (x0 : real -> Prop) := ~ (ex x0).
Definition term22 (x0 : nat -> Prop) := ~ (ex x0).
Definition term583 (x0 : real -> nat) (x1 : real) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2))) y0).
Definition term636 (x0 : real -> nat) (x1 : real) := fun y0 : real -> nat => (fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0.
Definition term628 (x0 : real -> nat) (x1 : real) := ((fun y0 : real => exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) x1) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term515 (x0 : real) := forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => (~ (real_le (real_of_num y3) y2)) \/ (real_le x0 y2)) y0 y1.
Definition term514 (x0 : real) := forall y0 : real, exists y1 : nat, (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0).
Definition term462 := forall y0 : real, exists y1 : nat, (fun y2 : real => fun y3 : nat => ~ (real_le (real_of_num y3) y2)) y0 y1.
Definition term460 (x0 : type1622) := forall y0 : real, exists y1 : nat, x0 y0 y1.
Definition term420 := forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0).
Definition term352 := forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1).
Definition term693 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0.
Definition term284 := ((NUMERAL (BIT1 0)) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term296 (x0 : real) := (fun y0 : real => (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) x0.
Definition term467 (x0 : real) (x1 : nat) := (fun y0 : nat => ~ (real_le (real_of_num y0) x0)) x1.
Definition term668 (x0 : real) (x1 : real) (x2 : real) := ((real_le x0 (real_sub x2 x1)) \/ (~ (real_le (real_add x0 x1) x2))) /\ ((~ (real_le x0 (real_sub x2 x1))) \/ (real_le (real_add x0 x1) x2)).
Definition term295 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term527 (x0 : real) (x1 : real -> nat) (x2 : real) := (fun y0 : nat => (~ (real_le (real_of_num y0) x2)) \/ (real_le x0 x2)) (x1 x2).
Definition term627 (x0 : real -> nat) (x1 : real) := and (exists y0 : real -> nat, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))).
Definition term602 (x0 : type1024) (x1 : Prop) := exists y0 : real -> nat, (x0 y0) /\ x1.
Definition term12 := forall y0 : real -> Prop, (~ ((forall y1 : real, (exists y2 : nat, y1 = (real_of_num y2)) -> y0 y1) = (forall y1 : nat, y0 (real_of_num y1)))) -> False.
Definition term507 (x0 : nat) (x1 : real) := or (~ (real_le (real_of_num x0) x1)).
Definition term44 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) x1.
Definition term106 (x0 : real -> Prop) (x1 : real) := fun y0 : nat => (x1 = (real_of_num y0)) /\ (~ (x0 x1)).
Definition term686 (x0 : real) (x1 : real) (x2 : real) := and ((real_le x0 (real_sub x2 x1)) \/ (~ (real_le (real_add x0 x1) x2))).
Definition term456 := (((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) /\ (~ (forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))).
Definition term707 (x0 : real) := fun y0 : real => forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0).
Definition term391 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term379 (x0 : real) := fun y0 : real => forall y1 : real, (real_le x0 (real_sub y0 y1)) = (real_le (real_add x0 y1) y0).
Definition term325 := fun y0 : real => forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0.
Definition term102 (x0 : real) (x1 : nat) := and (x0 = (real_of_num x1)).
Definition term41 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term242 (x0 : real -> Prop) (x1 : nat) := (x0 (real_of_num x1)) -> False.
Definition term677 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term661 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := exists y0 : real, (((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x2) /\ (forall y1 : real, (~ (real_le (real_of_num (x1 y1)) y1)) \/ (real_le x2 y1)))) /\ (forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term642 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := and (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))).
Definition term23 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term464 := fun y0 : real => fun y1 : nat => ~ (real_le (real_of_num y1) y0).
Definition term19 (x0 : real -> Prop) (x1 : real) := (exists y0 : nat, x1 = (real_of_num y0)) -> x0 x1.
Definition term749 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term759 (x0 : real -> nat) (x1 : real) := ~ (real_le x1 (real_of_num (x0 x1))).
Definition term280 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term168 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term47 (x0 : real -> Prop) := fun y0 : real => (exists y1 : nat, y0 = (real_of_num y1)) /\ (~ (x0 y0)).
Definition term847 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x0 x1) x2).
Definition term593 (x0 : real -> nat) (x1 : real) := fun y0 : real -> nat => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1))).
Definition term644 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term285 := S (Nat.add 0 0).
Definition term662 (x0 : real -> nat) (x1 : real) := fun y0 : real -> nat => exists y1 : real, (((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y0 y2)) y2)) \/ (real_le x1 y2)))) /\ (forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term827 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term724 := fun y0 : real => (forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) /\ (forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)).
Definition term269 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term657 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) (x3 : real) := (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))) /\ ((fun y0 : real => forall y1 : nat, ~ (real_le y0 (real_of_num y1))) x3).
Definition term837 (x0 : real -> nat) (x1 : real) := (x1 = x1) /\ (real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1).
Definition term656 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := @eq Prop ((((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1)))).
Definition term655 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := @eq Prop ((((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))) /\ (exists y0 : real, (fun y1 : real => forall y2 : nat, ~ (real_le y1 (real_of_num y2))) y0)).
Definition term434 := exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (exists y2 : nat, ~ (real_le (real_of_num y2) y1)) \/ (real_le y0 y1)).
Definition term348 := exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1).
Definition term347 := exists y0 : real, (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => exists y4 : nat, y3 = (real_of_num y4)) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term128 (x0 : real -> Prop) := exists y0 : real, (exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y1 : nat, x0 (real_of_num y1)).
Definition term259 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term93 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term853 (x0 : real -> nat) (x1 : real) := ~ (real_le (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term699 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => (~ (real_le x0 (real_sub x1 y1))) \/ (real_le (real_add x0 y1) x1)) y0.
Definition term694 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0.
Definition term781 (x0 : real -> nat) (x1 : real) := x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term238 (x0 : real) (x1 : nat) := imp (x0 = (real_of_num x1)).
Definition term253 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term836 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_le x0 x1))) -> real_le x2 x3.
Definition term317 (x0 : real) := fun y0 : real => (exists y1 : nat, y0 = (real_of_num y1)) -> (fun y1 : real => real_le y1 x0) y0.
Definition term632 (x0 : real -> nat) := exists y0 : real, (exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term804 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term389 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term37 (x0 : real) := or (forall y0 : nat, ~ (x0 = (real_of_num y0))).
Definition term219 (x0 : real -> Prop) := fun y0 : real => forall y1 : nat, (~ (y0 = (real_of_num y1))) \/ (x0 y0).
Definition term522 (x0 : real) (x1 : real) := exists y0 : nat, (fun y1 : real => fun y2 : nat => (~ (real_le (real_of_num y2) y1)) \/ (real_le x0 y1)) x1 y0.
Definition term378 (x0 : real) (x1 : real) := forall y0 : real, (real_le x0 (real_sub x1 y0)) = (real_le (real_add x0 y0) x1).
Definition term416 (x0 : real) := (fun y0 : real => forall y1 : nat, real_le (real_of_num y1) y0) x0.
Definition term125 (x0 : real) (x1 : real -> Prop) := (exists y0 : nat, (x0 = (real_of_num y0)) /\ (~ (x1 x0))) /\ (forall y0 : nat, x1 (real_of_num y0)).
Definition term64 (x0 : real -> Prop) := (exists y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y0 : nat, x0 (real_of_num y0)).
Definition term580 (x0 : real -> nat) := fun y0 : real => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((fun y1 : real => exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))) y0).
Definition term579 (x0 : real -> nat) (x1 : real) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real -> nat, (forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1))).
Definition term734 := fun y0 : real => ((fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, (~ (real_le y1 (real_sub y2 y3))) \/ (real_le (real_add y1 y3) y2)) y0).
Definition term712 (x0 : real) := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_le x0 (real_sub y1 y2))) \/ (real_le (real_add x0 y2) y1)) y0).
Definition term204 (x0 : real -> Prop) (x1 : real) := (forall y0 : nat, (fun y1 : nat => ~ (x1 = (real_of_num y1))) y0) \/ (x0 x1).
Definition term39 (x0 : real -> Prop) (x1 : real) := (forall y0 : nat, ~ (x1 = (real_of_num y0))) \/ (x0 x1).
Definition term312 (x0 : real) := forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> (fun y1 : real => real_le y1 x0) y0.
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term763 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term685 (x0 : real) (x1 : real) (x2 : real) := and ((fun y0 : real => (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) x2).
Definition term792 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term377 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 (real_sub x1 y0)) = (real_le (real_add x0 y0) x1).
Definition term790 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term430 (x0 : real) := fun y0 : real => (exists y1 : nat, ~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0).
Definition term188 (x0 : real) (x1 : real -> Prop) := exists y0 : nat, (fun y1 : nat => ((x0 = (real_of_num y1)) /\ (~ (x1 x0))) /\ (forall y2 : nat, x1 (real_of_num y2))) y0.
Definition term155 (x0 : real -> Prop) := exists y0 : nat, (fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0.
Definition term133 (x0 : real -> Prop) (x1 : real) := exists y0 : nat, (fun y1 : nat => (x1 = (real_of_num y1)) /\ (~ (x0 x1))) y0.
Definition term97 (x0 : real) := exists y0 : nat, (fun y1 : nat => x0 = (real_of_num y1)) y0.
Definition term394 (x0 : real) (x1 : nat) := real_le x0 (real_of_num x1).
Definition term631 (x0 : real -> nat) := fun y0 : real => (exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term689 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) x2) /\ ((fun y0 : real => (~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1)) x2).
Definition term6 (x0 : real -> Prop) := (((~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False) -> (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False) -> (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False.
Definition term239 (x0 : nat) (x1 : real -> Prop) (x2 : real) := (x2 = (real_of_num x0)) -> x1 x2.
Definition term660 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := fun y0 : real => (((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x2) /\ (forall y1 : real, (~ (real_le (real_of_num (x1 y1)) y1)) \/ (real_le x2 y1)))) /\ (forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term821 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term274 := real_mul (real_of_num (NUMERAL 0)).
Definition term832 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_le x1 x2).
Definition term709 (x0 : real) (x1 : real) := and ((fun y0 : real => forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) x1).
Definition term626 (x0 : real -> nat) (x1 : real) := and ((fun y0 : real => exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) x1).
Definition term122 (x0 : real -> Prop) (x1 : real) := and ((fun y0 : real => exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))) x1).
Definition term205 (x0 : real -> Prop) (x1 : real) := forall y0 : nat, ((fun y1 : nat => ~ (x1 = (real_of_num y1))) y0) \/ (x0 x1).
Definition term620 (x0 : real -> nat) (x1 : real) := (fun y0 : real => exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))) x1.
Definition term710 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)) x1.
Definition term708 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) x1.
Definition term413 (x0 : real) := exists y0 : nat, ~ (real_le (real_of_num y0) x0).
Definition term267 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term324 (x0 : real) := forall y0 : nat, real_le (real_of_num y0) x0.
Definition term802 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term540 (x0 : real) := exists y0 : real -> nat, (forall y1 : nat, real_le (real_of_num y1) x0) /\ ((fun y1 : real -> nat => forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2)) y0).
Definition term172 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2))) x1.
Definition term116 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))) x1.
Definition term437 := (~ ((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0))) \/ (exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)).
Definition term633 (x0 : real -> nat) (x1 : real) := (exists y0 : real -> nat, (fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term618 (x0 : real -> nat) := (exists y0 : real, (fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term603 := (exists y0 : real -> nat, (fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term329 := (exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0).
Definition term8 (x0 : real -> Prop) := ~ (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))).
Definition term423 := (~ (exists y0 : real, exists y1 : nat, y0 = (real_of_num y1))) \/ (~ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)).
Definition term530 (x0 : real -> nat) (x1 : real) := fun y0 : real => (~ (real_le (real_of_num (x0 y0)) y0)) \/ (real_le x1 y0).
Definition term517 (x0 : real) := fun y0 : real => fun y1 : nat => (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0).
Definition term222 (x0 : real -> Prop) (x1 : real) (x2 : nat) := (fun y0 : nat => (~ (x1 = (real_of_num y0))) \/ (x0 x1)) x2.
Definition term55 (x0 : real -> Prop) (x1 : nat) := (fun y0 : nat => x0 (real_of_num y0)) x1.
Definition term842 (x0 : real -> nat) (x1 : real) := ~ (real_le (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term279 (x0 : real) := real_ge (real_sub (real_sub x0 (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term683 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1))) x2.
Definition term479 (x0 : real -> nat) := forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0).
Definition term844 (x0 : real) (x1 : real) (x2 : real) := ~ (real_le (real_add x0 x1) x2).
Definition term531 (x0 : real) (x1 : real -> nat) := forall y0 : real, (fun y1 : real => fun y2 : nat => (~ (real_le (real_of_num y2) y1)) \/ (real_le x0 y1)) y0 (x1 y0).
Definition term770 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term584 (x0 : real -> nat) (x1 : real) := exists y0 : real -> nat, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((fun y1 : real -> nat => (forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2))) y0).
Definition term241 (x0 : real -> Prop) (x1 : nat) := (~ (x0 (real_of_num x1))) -> x0 (real_of_num x1).
Definition term508 (x0 : nat) (x1 : real) (x2 : real) := ((fun y0 : nat => ~ (real_le (real_of_num y0) x2)) x0) \/ (real_le x1 x2).
Definition term20 (x0 : real -> Prop) := fun y0 : real => (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0.
Definition term549 (x0 : real) := fun y0 : real -> nat => (forall y1 : nat, real_le (real_of_num y1) x0) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1)).
Definition term573 (x0 : real) := (fun y0 : real => exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))) x0.
Definition term599 := and (exists y0 : real -> nat, exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))).
Definition term94 (x0 : real -> Prop) (x1 : real) := (exists y0 : nat, (fun y1 : nat => x1 = (real_of_num y1)) y0) /\ (~ (x0 x1)).
Definition term169 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term359 := (((~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False) -> (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False) -> (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term164 (x0 : real -> Prop) := fun y0 : nat => ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))) \/ (exists y1 : real, exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))).
Definition term601 (x0 : type1024) (x1 : Prop) := (exists y0 : real -> nat, x0 y0) /\ x1.
Definition term112 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term92 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term397 := fun y0 : real => exists y1 : nat, real_le y0 (real_of_num y1).
Definition term292 := fun y0 : real => exists y1 : nat, y0 = (real_of_num y1).
Definition term410 (x0 : nat) (x1 : real) := ~ (real_le (real_of_num x0) x1).
Definition term634 (x0 : real -> nat) (x1 : real) := exists y0 : real -> nat, ((fun y1 : real -> nat => ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2)))) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term604 := exists y0 : real -> nat, ((fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term784 (x0 : real -> nat) (x1 : real) := (~ ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term165 (x0 : real -> Prop) := exists y0 : nat, ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))) \/ (exists y1 : real, exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))).
Definition term252 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term440 (x0 : real) := forall y0 : nat, ~ ((fun y1 : nat => real_le x0 (real_of_num y1)) y0).
Definition term25 (x0 : real) := forall y0 : nat, ~ ((fun y1 : nat => x0 = (real_of_num y1)) y0).
Definition term14 (x0 : real -> Prop) (x1 : nat) := x0 (real_of_num x1).
Definition term218 (x0 : real -> Prop) (x1 : real) := forall y0 : nat, (~ (x1 = (real_of_num y0))) \/ (x0 x1).
Definition term630 (x0 : real -> nat) := fun y0 : real => ((fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term746 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term358 := ((~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False) -> (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term395 (x0 : real) := fun y0 : nat => real_le x0 (real_of_num y0).
Definition term729 := fun y0 : real => forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1).
Definition term728 := fun y0 : real => forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1)).
Definition term673 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) /\ ((~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)).
Definition term381 := fun y0 : real => forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1).
Definition term351 := imp (((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)).
Definition term350 := imp (((exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => exists y4 : nat, y3 = (real_of_num y4)) y2) -> real_le y2 y1) -> real_le y0 y1)).
Definition term86 (x0 : real -> Prop) := fun y0 : nat => (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ ((fun y1 : nat => ~ (x0 (real_of_num y1))) y0).
Definition term127 (x0 : real -> Prop) := fun y0 : real => (exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y1 : nat, x0 (real_of_num y1)).
Definition term534 (x0 : real) := fun y0 : real -> nat => forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1).
Definition term533 (x0 : real) := fun y0 : real -> nat => forall y1 : real, (fun y2 : real => fun y3 : nat => (~ (real_le (real_of_num y3) y2)) \/ (real_le x0 y2)) y1 (y0 y1).
Definition term480 := fun y0 : real -> nat => forall y1 : real, (fun y2 : real => fun y3 : nat => ~ (real_le (real_of_num y3) y2)) y1 (y0 y1).
Definition term700 (x0 : real) (x1 : real) := forall y0 : real, (~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1).
Definition term50 (x0 : real -> Prop) := forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0).
Definition term108 (x0 : real -> Prop) := fun y0 : real => exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0)).
Definition term839 (x0 : real -> nat) (x1 : real) := (((real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0))))) /\ ((x1 = x1) /\ (real_le (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) x1))) -> real_le (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) x1.
Definition term193 (x0 : nat) (x1 : real) (x2 : real -> Prop) := fun y0 : nat => ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x2 y1)) /\ (~ (x2 (real_of_num x0)))) \/ ((fun y1 : nat => ((x1 = (real_of_num y1)) /\ (~ (x2 x1))) /\ (forall y2 : nat, x2 (real_of_num y2))) y0).
Definition term262 (x0 : real) := real_sub (real_add x0 (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term752 (x0 : real -> nat) (x1 : real) := (fun y0 : real => ~ (real_le (real_of_num (x0 y0)) y0)) x1.
Definition term326 := fun y0 : real => forall y1 : nat, real_le (real_of_num y1) y0.
Definition term123 (x0 : real -> Prop) (x1 : real) := and (exists y0 : nat, (x1 = (real_of_num y0)) /\ (~ (x0 x1))).
Definition term33 (x0 : real) := and (exists y0 : nat, x0 = (real_of_num y0)).
Definition term229 (x0 : nat) := ~ ((real_of_num x0) = (real_of_num x0)).
Definition term411 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => real_le (real_of_num y1) x0) y0).
Definition term561 := or (exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0).
Definition term111 (x0 : real -> Prop) := (exists y0 : real, exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y0 : nat, x0 (real_of_num y0)).
Definition term513 (x0 : real) := fun y0 : real => exists y1 : nat, (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0).
Definition term682 (x0 : real) (x1 : real) := fun y0 : real => (~ (real_le x0 (real_sub x1 y0))) \/ (real_le (real_add x0 y0) x1).
Definition term819 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term192 (x0 : nat) (x1 : nat) (x2 : real) (x3 : real -> Prop) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x3 y0)) /\ (~ (x3 (real_of_num x0)))) \/ (((x2 = (real_of_num x1)) /\ (~ (x3 x2))) /\ (forall y0 : nat, x3 (real_of_num y0))).
Definition term748 (x0 : real) := (fun y0 : real => forall y1 : nat, ~ (y0 = (real_of_num y1))) x0.
Definition term652 (x0 : real) := (fun y0 : real => forall y1 : nat, ~ (real_le y0 (real_of_num y1))) x0.
Definition term144 (x0 : real -> Prop) := fun y0 : real => exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2)).
Definition term69 (x0 : real -> Prop) := or ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) /\ (~ (forall y0 : nat, x0 (real_of_num y0)))).
Definition term725 := forall y0 : real, (forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) /\ (forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)).
Definition term703 (x0 : real) := forall y0 : real, (forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0))) /\ (forall y1 : real, (~ (real_le x0 (real_sub y0 y1))) \/ (real_le (real_add x0 y1) y0)).
Definition term79 (x0 : real -> Prop) (x1 : nat) := (fun y0 : nat => ~ (x0 (real_of_num y0))) x1.
Definition term558 (x0 : real -> nat) := (fun y0 : real -> nat => (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) x0.
Definition term494 (x0 : real -> nat) := (forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0)).
Definition term160 (x0 : real -> Prop) (x1 : nat) := or ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (~ (x0 (real_of_num x1)))).
Definition term851 (x0 : real -> nat) (x1 : real) := real_le (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term258 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term826 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term496 := fun y0 : real -> nat => (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1)).
Definition term532 (x0 : real -> nat) (x1 : real) := forall y0 : real, (~ (real_le (real_of_num (x0 y0)) y0)) \/ (real_le x1 y0).
Definition term30 (x0 : real) := fun y0 : nat => ~ (x0 = (real_of_num y0)).
Definition term807 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term829 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term799 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term385 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term250 := real_of_num (NUMERAL (BIT1 0)).
Definition term795 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term823 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term613 (x0 : real -> nat) := ((fun y0 : real -> nat => exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) x0) /\ (exists y0 : real, forall y1 : nat, ~ (real_le y0 (real_of_num y1))).
Definition term236 (x0 : real) (x1 : nat) := ~ (~ (x0 = (real_of_num x1))).
Definition term407 (x0 : real) := exists y0 : nat, ~ ((fun y1 : nat => real_le (real_of_num y1) x0) y0).
Definition term54 (x0 : real -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => x0 (real_of_num y1)) y0).
Definition term372 := (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)).
Definition term226 (x0 : real -> Prop) (x1 : real) := @eq Prop ((fun y0 : real => ~ (x0 y0)) x1).
Definition term623 (x0 : real -> nat) := and (exists y0 : real, (fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0).
Definition term303 := and (exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0).
Definition term119 (x0 : real -> Prop) := and (exists y0 : real, (fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0).
Definition term370 := imp (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term557 := exists y0 : real -> nat, ((fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0) \/ (exists y1 : real, exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))).
Definition term852 (x0 : real -> nat) (x1 : real) := (~ (real_le (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) -> real_le (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term278 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term743 := forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (~ (real_le y1 (real_sub y2 y3))) \/ (real_le (real_add y1 y3) y2)) y0.
Definition term738 := forall y0 : real, (fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0.
Definition term721 (x0 : real) := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le x0 (real_sub y1 y2))) \/ (real_le (real_add x0 y2) y1)) y0.
Definition term716 (x0 : real) := forall y0 : real, (fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0.
Definition term585 (x0 : real) (x1 : real -> nat) := (fun y0 : real -> nat => (forall y1 : nat, real_le (real_of_num y1) x0) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1))) x1.
Definition term803 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term275 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term733 (x0 : real) := ((fun y0 : real => forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) x0) /\ ((fun y0 : real => forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)) x0).
Definition term443 (x0 : real) (x1 : nat) := ~ (real_le x0 (real_of_num x1)).
Definition term366 := (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)).
Definition term103 (x0 : nat) (x1 : real -> Prop) (x2 : real) := ((fun y0 : nat => x2 = (real_of_num y0)) x0) /\ (~ (x1 x2)).
Definition term310 (x0 : real) := forall y0 : real, ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) -> real_le y0 x0.
Definition term848 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 x2) x1) -> real_le x0 (real_sub x1 x2).
Definition term774 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term813 (x0 : real) := ~ (x0 = x0).
Definition term828 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term619 (x0 : real -> nat) := exists y0 : real, ((fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term690 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0) /\ ((fun y1 : real => (~ (real_le x0 (real_sub x1 y1))) \/ (real_le (real_add x0 y1) x1)) y0).
Definition term698 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 (real_sub x1 y1))) \/ (real_le (real_add x0 y1) x1)) y0.
Definition term811 (x0 : real -> nat) (x1 : real) := ~ ((real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term565 (x0 : real -> nat) := or ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))).
Definition term436 := or ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0))).
Definition term56 (x0 : real -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (real_of_num y0)) x1).
Definition term415 := forall y0 : real, ~ ((fun y1 : real => forall y2 : nat, real_le (real_of_num y2) y1) y0).
Definition term401 := forall y0 : real, ~ ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0).
Definition term571 (x0 : real -> nat) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ (exists y0 : real, (fun y1 : real => exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))) y0).
Definition term335 (x0 : real) := imp (forall y0 : real, ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) -> real_le y0 x0).
Definition term501 (x0 : real) := fun y0 : nat => (fun y1 : nat => ~ (real_le (real_of_num y1) x0)) y0.
Definition term207 (x0 : real) := fun y0 : nat => (fun y1 : nat => ~ (x0 = (real_of_num y1))) y0.
Definition term80 (x0 : real -> Prop) := fun y0 : nat => (fun y1 : nat => ~ (x0 (real_of_num y1))) y0.
Definition term664 (x0 : real -> nat) := fun y0 : real => exists y1 : real -> nat, exists y2 : real, (((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y0) /\ (forall y3 : real, (~ (real_le (real_of_num (y1 y3)) y3)) \/ (real_le y0 y3)))) /\ (forall y3 : nat, ~ (real_le y2 (real_of_num y3))).
Definition term249 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term424 := (forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0)).
Definition term46 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => (exists y2 : nat, y1 = (real_of_num y2)) -> x0 y1) y0).
Definition term773 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term445 (x0 : real) := fun y0 : nat => ~ (real_le x0 (real_of_num y0)).
Definition term152 (x0 : real -> Prop) := exists y0 : nat, ((fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0) \/ (exists y1 : real, exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))).
Definition term184 (x0 : nat) (x1 : real) (x2 : real -> Prop) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x2 y0)) /\ (~ (x2 (real_of_num x0)))) \/ (exists y0 : nat, (fun y1 : nat => ((x1 = (real_of_num y1)) /\ (~ (x2 x1))) /\ (forall y2 : nat, x2 (real_of_num y2))) y0).
Definition term678 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term859 (x0 : real -> nat) (x1 : real) := imp (~ (~ (real_le (real_of_num (x0 x1)) x1))).
Definition term61 (x0 : real -> Prop) := and (~ (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0)).
Definition term647 (x0 : real -> nat) (x1 : real) := exists y0 : real -> nat, (((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((forall y1 : nat, real_le (real_of_num y1) x1) /\ (forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x1 y1)))) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term606 := fun y0 : real -> nat => (fun y1 : real -> nat => exists y2 : real, exists y3 : real -> nat, ((forall y4 : real, forall y5 : nat, ~ (y4 = (real_of_num y5))) \/ (forall y4 : real, ~ (real_le (real_of_num (y1 y4)) y4))) \/ ((forall y4 : nat, real_le (real_of_num y4) y2) /\ (forall y4 : real, (~ (real_le (real_of_num (y3 y4)) y4)) \/ (real_le y2 y4)))) y0.
Definition term616 := fun y0 : real -> nat => (exists y1 : real, exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (y0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) /\ (exists y1 : real, forall y2 : nat, ~ (real_le y1 (real_of_num y2))).
Definition term843 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le (real_add x0 x2) x1))) -> real_le x0 (real_sub x1 x2).
Definition term755 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.add x0 x1)))) -> (real_add (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.add x0 x1)).
Definition term386 := fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term833 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3)).
Definition term545 (x0 : real) := @eq Prop ((forall y0 : nat, real_le (real_of_num y0) x0) /\ (exists y0 : real -> nat, forall y1 : real, (~ (real_le (real_of_num (y0 y1)) y1)) \/ (real_le x0 y1))).
Definition term544 (x0 : real) := @eq Prop ((forall y0 : nat, real_le (real_of_num y0) x0) /\ (exists y0 : real -> nat, (fun y1 : real -> nat => forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x0 y2)) y0)).
Definition term83 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (exists y0 : nat, ~ (x0 (real_of_num y0)))).
Definition term82 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (exists y0 : nat, (fun y1 : nat => ~ (x0 (real_of_num y1))) y0)).
Definition term806 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term675 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term199 (x0 : real -> Prop) := exists y0 : nat, exists y1 : real, exists y2 : nat, ((forall y3 : real, (forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (x0 y3)) /\ (~ (x0 (real_of_num y0)))) \/ (((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))).
Definition term354 := (((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1).
Definition term353 := (((exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => exists y3 : nat, y2 = (real_of_num y3)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => exists y4 : nat, y3 = (real_of_num y4)) y2) -> real_le y2 y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1).
Definition term143 (x0 : real) (x1 : real -> Prop) := exists y0 : nat, ((x0 = (real_of_num y0)) /\ (~ (x1 x0))) /\ (forall y1 : nat, x1 (real_of_num y1)).
Definition term441 (x0 : real) (x1 : nat) := (fun y0 : nat => real_le x0 (real_of_num y0)) x1.
Definition term499 (x0 : real) (x1 : real) := (exists y0 : nat, (fun y1 : nat => ~ (real_le (real_of_num y1) x1)) y0) \/ (real_le x0 x1).
Definition term429 (x0 : real) (x1 : real) := (exists y0 : nat, ~ (real_le (real_of_num y0) x1)) \/ (real_le x0 x1).
Definition term58 (x0 : real -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (real_of_num y1)) y0).
Definition term555 (x0 : type1024) (x1 : Prop) := exists y0 : real -> nat, (x0 y0) \/ x1.
Definition term373 := imp (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))).
Definition term809 (x0 : real -> nat) (x1 : real) := (((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0))))) /\ ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term428 (x0 : real) (x1 : real) := (~ (forall y0 : nat, real_le (real_of_num y0) x1)) \/ (real_le x0 x1).
Definition term855 (x0 : real -> nat) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le (real_of_num (x0 x2)) x2)) \/ (real_le x1 x2)).
Definition term101 (x0 : real) (x1 : nat) := and ((fun y0 : nat => x0 = (real_of_num y0)) x1).
Definition term444 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => real_le x0 (real_of_num y1)) y0).
Definition term29 (x0 : real) := fun y0 : nat => ~ ((fun y1 : nat => x0 = (real_of_num y1)) y0).
Definition term442 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => real_le x0 (real_of_num y0)) x1).
Definition term27 (x0 : real) (x1 : nat) := ~ ((fun y0 : nat => x0 = (real_of_num y0)) x1).
Definition term136 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : nat, (x0 = (real_of_num y0)) /\ (~ (x1 x0))) /\ (forall y0 : nat, x1 (real_of_num y0))).
Definition term135 (x0 : real) (x1 : real -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x0 = (real_of_num y1)) /\ (~ (x1 x0))) y0) /\ (forall y0 : nat, x1 (real_of_num y0))).
Definition term121 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y0 : nat, x0 (real_of_num y0))).
Definition term120 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0) /\ (forall y0 : nat, x0 (real_of_num y0))).
Definition term7 (x0 : real -> Prop) := (((~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False) -> (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False) -> ((~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False) -> (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False.
Definition term305 (x0 : real) := imp ((fun y0 : real => exists y1 : nat, y0 = (real_of_num y1)) x0).
Definition term1 (x0 : real -> Prop) := forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0.
Definition term421 := or (~ (exists y0 : real, exists y1 : nat, y0 = (real_of_num y1))).
Definition term36 (x0 : real) := or (~ (exists y0 : nat, x0 = (real_of_num y0))).
Definition term225 (x0 : real -> Prop) (x1 : nat) := (fun y0 : real => ~ (x0 y0)) (real_of_num x1).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term316 (x0 : real) (x1 : real) := (exists y0 : nat, x1 = (real_of_num y0)) -> (fun y0 : real => real_le y0 x0) x1.
Definition term355 := (~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1))) -> False.
Definition term3 (x0 : real -> Prop) := (~ ((forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) = (forall y0 : nat, x0 (real_of_num y0)))) -> False.
Definition term299 (x0 : real) := @eq Prop ((fun y0 : real => (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) x0).
Definition term612 (x0 : real -> nat) := and (exists y0 : real, exists y1 : real -> nat, ((forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (x0 y2)) y2))) \/ ((forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))).
Definition term304 := and (exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)).
Definition term110 (x0 : real -> Prop) := and (exists y0 : real, exists y1 : nat, (y0 = (real_of_num y1)) /\ (~ (x0 y0))).
Definition term503 (x0 : real) := or (exists y0 : nat, (fun y1 : nat => ~ (real_le (real_of_num y1) x0)) y0).
Definition term156 (x0 : real -> Prop) := or (exists y0 : nat, (fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0).
Definition term808 (x0 : real -> nat) (x1 : real) := ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0))))) /\ ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term406 (x0 : real) := ~ (forall y0 : nat, real_le (real_of_num y0) x0).
Definition term371 := (forall y0 : real, ~ (real_le y0 (real_sub y0 (real_of_num (NUMERAL (BIT1 0)))))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) = (real_le (real_add y0 y2) y1)) -> False.
Definition term786 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term487 := exists y0 : real -> nat, (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ ((fun y1 : real -> nat => forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2)) y0).
Definition term511 (x0 : real) (x1 : real) := fun y0 : nat => (~ (real_le (real_of_num y0) x1)) \/ (real_le x0 x1).
Definition term780 (x0 : real -> nat) (x1 : real) := real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0))).
Definition term801 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term498 := or (exists y0 : real -> nat, (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))).
Definition term15 (x0 : real -> Prop) := fun y0 : nat => x0 (real_of_num y0).
Definition term375 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_sub x1 x2).
Definition term455 := and (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, exists y1 : nat, ~ (real_le (real_of_num y1) y0))) \/ (exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (exists y2 : nat, ~ (real_le (real_of_num y2) y1)) \/ (real_le y0 y1)))).
Definition term272 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term281 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term178 (x0 : nat) (x1 : real) (x2 : real -> Prop) := ((forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x2 y0)) /\ (~ (x2 (real_of_num x0)))) \/ (exists y0 : nat, ((x1 = (real_of_num y0)) /\ (~ (x2 x1))) /\ (forall y1 : nat, x2 (real_of_num y1))).
Definition term789 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term650 (x0 : real -> nat) (x1 : real -> nat) (x2 : real) := (((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((forall y0 : nat, real_le (real_of_num y0) x2) /\ (forall y0 : real, (~ (real_le (real_of_num (x1 y0)) y0)) \/ (real_le x2 y0)))) /\ (exists y0 : real, (fun y1 : real => forall y2 : nat, ~ (real_le y1 (real_of_num y2))) y0).
Definition term854 (x0 : real) (x1 : real -> nat) (x2 : real) := (real_le x0 x2) \/ (~ (real_le (real_of_num (x1 x2)) x2)).
Definition term315 (x0 : real) (x1 : real) := (fun y0 : real => real_le y0 x0) x1.
Definition term67 (x0 : real -> Prop) := (forall y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) -> x0 y0) /\ (~ (forall y0 : nat, x0 (real_of_num y0))).
Definition term308 (x0 : real) := fun y0 : real => ((fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0) -> real_le y0 x0.
Definition term459 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term364 := imp (forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))).
Definition term592 (x0 : real -> nat) (x1 : real) := fun y0 : real -> nat => ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (x0 y1)) y1))) \/ ((fun y1 : real -> nat => (forall y2 : nat, real_le (real_of_num y2) x1) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le x1 y2))) y0).
Definition term277 := real_add (real_of_num (NUMERAL 0)).
Definition term287 (x0 : real) := (~ (~ (real_le x0 (real_sub x0 (real_of_num (NUMERAL (BIT1 0))))))) -> False.
Definition term757 (x0 : real) (x1 : nat) := (x0 = (real_of_num x1)) -> False.
Definition term383 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term732 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (~ (real_le y0 (real_sub y1 y2))) \/ (real_le (real_add y0 y2) y1)) x0.
Definition term730 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y0 (real_sub y1 y2)) \/ (~ (real_le (real_add y0 y2) y1))) x0.
Definition term306 (x0 : real) (x1 : real) := ((fun y0 : real => exists y1 : nat, y0 = (real_of_num y1)) x0) -> real_le x0 x1.
Definition term126 (x0 : real -> Prop) := fun y0 : real => ((fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0) /\ (forall y1 : nat, x0 (real_of_num y1)).
Definition term777 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term547 (x0 : real -> nat) (x1 : real) := (forall y0 : nat, real_le (real_of_num y0) x1) /\ (forall y0 : real, (~ (real_le (real_of_num (x0 y0)) y0)) \/ (real_le x1 y0)).
Definition term432 (x0 : real) := (forall y0 : nat, real_le (real_of_num y0) x0) /\ (forall y0 : real, (exists y1 : nat, ~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0)).
Definition term344 (x0 : real) := (forall y0 : nat, real_le (real_of_num y0) x0) /\ (forall y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) -> real_le x0 y0).
Definition term77 (x0 : real -> Prop) := (forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (exists y0 : nat, (fun y1 : nat => ~ (x0 (real_of_num y1))) y0).
Definition term62 (x0 : real -> Prop) := and (exists y0 : real, (exists y1 : nat, y0 = (real_of_num y1)) /\ (~ (x0 y0))).
Definition term52 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term182 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term85 (x0 : real -> Prop) (x1 : nat) := (forall y0 : real, (forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (x0 y0)) /\ (~ (x0 (real_of_num x1))).
Definition term695 (x0 : real) (x1 : real) := forall y0 : real, (real_le x0 (real_sub x1 y0)) \/ (~ (real_le (real_add x0 y0) x1)).
Definition term356 := ~ ((((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)) -> forall y0 : real, exists y1 : nat, real_le y0 (real_of_num y1)).
Definition term726 := forall y0 : real, ((fun y1 : real => forall y2 : real, forall y3 : real, (real_le y1 (real_sub y2 y3)) \/ (~ (real_le (real_add y1 y3) y2))) y0) /\ ((fun y1 : real => forall y2 : real, forall y3 : real, (~ (real_le y1 (real_sub y2 y3))) \/ (real_le (real_add y1 y3) y2)) y0).
Definition term704 (x0 : real) := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_le x0 (real_sub y1 y2)) \/ (~ (real_le (real_add x0 y2) y1))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_le x0 (real_sub y1 y2))) \/ (real_le (real_add x0 y2) y1)) y0).
Definition term679 (x0 : real) (x1 : real) := forall y0 : real, ((fun y1 : real => (real_le x0 (real_sub x1 y1)) \/ (~ (real_le (real_add x0 y1) x1))) y0) /\ ((fun y1 : real => (~ (real_le x0 (real_sub x1 y1))) \/ (real_le (real_add x0 y1) x1)) y0).
Definition term96 (x0 : real) := fun y0 : nat => (fun y1 : nat => x0 = (real_of_num y1)) y0.
Definition term216 (x0 : real -> Prop) (x1 : real) := fun y0 : nat => ((fun y1 : nat => ~ (x1 = (real_of_num y1))) y0) \/ (x0 x1).
Definition term764 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term194 (x0 : nat) (x1 : real) (x2 : real -> Prop) := fun y0 : nat => ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x2 y1)) /\ (~ (x2 (real_of_num x0)))) \/ (((x1 = (real_of_num y0)) /\ (~ (x2 x1))) /\ (forall y1 : nat, x2 (real_of_num y1))).
Definition term810 (x0 : real -> nat) (x1 : real) := (~ ((real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_of_num (Nat.add (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0))))) (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term32 (x0 : real -> Prop) (x1 : real) := ~ (x0 x1).
Definition term439 (x0 : real) := ~ (exists y0 : nat, real_le x0 (real_of_num y0)).
Definition term24 (x0 : real) := ~ (exists y0 : nat, x0 = (real_of_num y0)).
Definition term570 := exists y0 : real -> nat, ((forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) \/ (exists y1 : real, exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))).
Definition term215 (x0 : nat) (x1 : real -> Prop) (x2 : real) := (~ (x2 = (real_of_num x0))) \/ (x1 x2).
Definition term255 := NUMERAL (BIT1 0).
Definition term322 (x0 : real) := fun y0 : nat => (fun y1 : real => real_le y1 x0) (real_of_num y0).
Definition term750 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term150 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) \/ x1.
Definition term785 (x0 : real -> nat) (x1 : real) := ~ ((real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_add (real_of_num (x0 (real_sub x1 (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term425 := ~ ((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)).
Definition term268 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term762 (x0 : Prop) := x0 -> ~ x0.
Definition term578 (x0 : real -> nat) (x1 : real) := ((forall y0 : real, forall y1 : nat, ~ (y0 = (real_of_num y1))) \/ (forall y0 : real, ~ (real_le (real_of_num (x0 y0)) y0))) \/ ((fun y0 : real => exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2))) x1).
Definition term706 (x0 : real) := fun y0 : real => forall y1 : real, (real_le x0 (real_sub y0 y1)) \/ (~ (real_le (real_add x0 y1) y0)).
Definition term163 (x0 : real -> Prop) := fun y0 : nat => ((fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0) \/ (exists y1 : real, exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))).
Definition term454 := and (((exists y0 : real, exists y1 : nat, y0 = (real_of_num y1)) /\ (exists y0 : real, forall y1 : nat, real_le (real_of_num y1) y0)) -> exists y0 : real, (forall y1 : nat, real_le (real_of_num y1) y0) /\ (forall y1 : real, (forall y2 : nat, real_le (real_of_num y2) y1) -> real_le y0 y1)).
Definition term264 (x0 : real) := real_sub (real_add x0 (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term772 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term131 (x0 : real -> Prop) (x1 : real) (x2 : nat) := (fun y0 : nat => (x1 = (real_of_num y0)) /\ (~ (x0 x1))) x2.
Definition term519 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : real => fun y1 : nat => (~ (real_le (real_of_num y1) y0)) \/ (real_le x0 y0)) x1 x2.
Definition term221 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : nat, (~ (y0 = (real_of_num y1))) \/ (x0 y0)) x1.
Definition term654 := exists y0 : real, (fun y1 : real => forall y2 : nat, ~ (real_le y1 (real_of_num y2))) y0.
Definition term622 (x0 : real -> nat) := exists y0 : real, (fun y1 : real => exists y2 : real -> nat, ((forall y3 : real, forall y4 : nat, ~ (y3 = (real_of_num y4))) \/ (forall y3 : real, ~ (real_le (real_of_num (x0 y3)) y3))) \/ ((forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3)))) y0.
Definition term575 := exists y0 : real, (fun y1 : real => exists y2 : real -> nat, (forall y3 : nat, real_le (real_of_num y3) y1) /\ (forall y3 : real, (~ (real_le (real_of_num (y2 y3)) y3)) \/ (real_le y1 y3))) y0.
Definition term301 := exists y0 : real, (fun y1 : real => exists y2 : nat, y1 = (real_of_num y2)) y0.
Definition term174 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x0 y1))) /\ (forall y3 : nat, x0 (real_of_num y3))) y0.
Definition term118 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => exists y2 : nat, (y1 = (real_of_num y2)) /\ (~ (x0 y1))) y0.
Definition term78 (x0 : real -> Prop) := exists y0 : nat, (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ ((fun y1 : nat => ~ (x0 (real_of_num y1))) y0).
Definition term179 (x0 : nat) (x1 : real -> Prop) := fun y0 : real => ((forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x1 y1)) /\ (~ (x1 (real_of_num x0)))) \/ ((fun y1 : real => exists y2 : nat, ((y1 = (real_of_num y2)) /\ (~ (x1 y1))) /\ (forall y3 : nat, x1 (real_of_num y3))) y0).
Definition term563 := @eq Prop ((exists y0 : real -> nat, (forall y1 : real, forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (forall y1 : real, ~ (real_le (real_of_num (y0 y1)) y1))) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))).
Definition term562 := @eq Prop ((exists y0 : real -> nat, (fun y1 : real -> nat => (forall y2 : real, forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (forall y2 : real, ~ (real_le (real_of_num (y1 y2)) y2))) y0) \/ (exists y0 : real, exists y1 : real -> nat, (forall y2 : nat, real_le (real_of_num y2) y0) /\ (forall y2 : real, (~ (real_le (real_of_num (y1 y2)) y2)) \/ (real_le y0 y2)))).
Definition term158 (x0 : real -> Prop) := @eq Prop ((exists y0 : nat, (forall y1 : real, (forall y2 : nat, ~ (y1 = (real_of_num y2))) \/ (x0 y1)) /\ (~ (x0 (real_of_num y0)))) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2)))).
Definition term157 (x0 : real -> Prop) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : real, (forall y3 : nat, ~ (y2 = (real_of_num y3))) \/ (x0 y2)) /\ (~ (x0 (real_of_num y1)))) y0) \/ (exists y0 : real, exists y1 : nat, ((y0 = (real_of_num y1)) /\ (~ (x0 y0))) /\ (forall y2 : nat, x0 (real_of_num y2)))).
