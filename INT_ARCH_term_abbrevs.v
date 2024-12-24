Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term535 (x0 : nat) := ~ (exists y0 : nat, Peano.le x0 y0).
Definition term847 (x0 : int -> nat) (x1 : int) (x2 : int) := int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2).
Definition term120 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term1115 (x0 : int) (x1 : int) (x2 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ ((fun y0 : int => int_lt x0 (int_mul y0 x1)) x2).
Definition term355 (x0 : nat) (x1 : int) := real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term256 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term319 (x0 : int) (x1 : nat) (x2 : int) := ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term1091 (x0 : int) (x1 : int) (x2 : int) := (int_lt x0 (int_mul x1 x2)) -> False.
Definition term216 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term148 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term642 := exists y0 : int, forall y1 : nat, ~ (int_le y0 (int_of_num y1)).
Definition term799 (x0 : int -> nat) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))))) -> int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term388 (x0 : int) (x1 : int) (x2 : nat) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_of_num x2)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term1160 (x0 : type1551) := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (x0 y0 y1) y1)).
Definition term950 (x0 : type1551) := fun y0 : int => forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt y0 (int_mul (x0 y0 y1) y1)).
Definition term877 := fun y0 : int => forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1)).
Definition term777 (x0 : int) := fun y0 : int => forall y1 : int, ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le y0 y1))) \/ (int_le (int_mul x0 y0) (int_mul x0 y1)).
Definition term716 (x0 : int) := fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le y0 y1)) -> int_le (int_mul x0 y0) (int_mul x0 y1).
Definition term708 := fun y0 : int => forall y1 : int, (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> exists y3 : nat, int_le y2 (int_of_num y3)) -> (forall y2 : int, exists y3 : nat, int_le y2 (int_of_num y3)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : int, int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y2 y0))) -> (forall y2 : int, forall y3 : nat, forall y4 : int, ((int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y3)) /\ (int_le (int_mul (int_of_num y3) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4))) -> int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_le y3 y4)) -> int_le (int_mul y2 y3) (int_mul y2 y4)) -> ~ (forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y2)).
Definition term707 := fun y0 : int => forall y1 : int, (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> exists y3 : nat, int_le y2 (int_of_num y3)) -> (forall y2 : int, exists y3 : nat, int_le y2 (int_of_num y3)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : int, int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y2 y0))) -> (forall y2 : int, forall y3 : nat, forall y4 : int, ((int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y3)) /\ (int_le (int_mul (int_of_num y3) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4))) -> int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_le y3 y4)) -> int_le (int_mul y2 y3) (int_mul y2 y4)) -> (forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y2)) -> False.
Definition term1030 (x0 : int) (x1 : int) (x2 : int) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term197 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1168 (x0 : type1551) (x1 : int) := (fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (x0 y0 y1) y1))) x1.
Definition term991 (x0 : type1551) (x1 : int) := (fun y0 : int => forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt y0 (int_mul (x0 y0 y1) y1))) x1.
Definition term785 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le y0 y1))) \/ (int_le (int_mul x0 y0) (int_mul x0 y1))) x1.
Definition term358 (x0 : int) (x1 : nat) (x2 : int) := and ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) /\ (real_le (real_mul (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_int x2)))).
Definition term211 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term637 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term372 (x0 : nat) (x1 : int) := real_sub (real_mul (real_of_num x0) (real_of_int x1)).
Definition term154 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term80 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term636 (x0 : int -> Prop) := ~ (all x0).
Definition term543 (x0 : nat -> Prop) := ~ (all x0).
Definition term558 := (~ False) -> False.
Definition term570 := (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False.
Definition term523 := (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term315 := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0)).
Definition term91 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term268 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 (int_neg x1))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term779 := fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (int_le y1 y2))) \/ (int_le (int_mul y0 y1) (int_mul y0 y2)).
Definition term718 := fun y0 : int => forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2).
Definition term1014 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term1063 (x0 : type1551) (x1 : int) (x2 : int) := (x1 = x1) /\ (((int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2)) /\ (~ (int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2)))).
Definition term657 (x0 : int -> nat) (x1 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (int_le x1 (int_of_num (x0 x1)))).
Definition term1088 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x2) -> int_lt x1 (int_mul (x0 x1 x2) x2).
Definition term302 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term397 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term580 (x0 : int) := or (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term43 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term1065 (x0 : type1551) (x1 : int) (x2 : int) := ~ (int_lt x1 (int_mul (x0 x1 (int_neg x2)) (int_neg x2))).
Definition term845 (x0 : int -> nat) (x1 : int) (x2 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) /\ (int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2)).
Definition term770 (x0 : int) (x1 : int) (x2 : int) := or (~ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le x1 x2))).
Definition term156 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term281 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term190 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term263 (x0 : int) (x1 : int) := or (real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))).
Definition term564 := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False.
Definition term408 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term675 (x0 : int) (x1 : int) := fun y0 : int => int_lt x0 (int_mul y0 x1).
Definition term1159 (x0 : type1551) := fun y0 : int => (fun y1 : int => fun y2 : int -> int => forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ (int_lt y1 (int_mul (y2 y3) y3))) y0 (x0 y0).
Definition term949 (x0 : type1551) := fun y0 : int => (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y3)) \/ (int_lt y1 (int_mul (y2 y3) y3))) y0 (x0 y0).
Definition term735 (x0 : int -> nat) := fun y0 : int => (fun y1 : int => fun y2 : nat => int_le y1 (int_of_num y2)) y0 (x0 y0).
Definition term622 (x0 : int -> nat) := fun y0 : int => (fun y1 : int => fun y2 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (int_le y1 (int_of_num y2))) y0 (x0 y0).
Definition term726 (x0 : int) := (fun y0 : int => fun y1 : nat => int_le y0 (int_of_num y1)) x0.
Definition term283 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term550 := exists y0 : nat, forall y1 : nat, ~ (Peano.le y0 y1).
Definition term63 (x0 : int) := real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term191 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term672 (x0 : int) := imp (int_le (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term503 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term8 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((~ (int_lt (int_of_num (NUMERAL 0)) x0)) /\ (~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))).
Definition term269 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul x0 (int_neg x1))).
Definition term713 (x0 : int) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le x0 x2)) -> int_le (int_mul x1 x0) (int_mul x1 x2).
Definition term416 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)) (real_of_num (NUMERAL 0)).
Definition term854 (x0 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> exists y1 : int, int_lt x0 (int_mul y1 y0).
Definition term497 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1).
Definition term79 (x0 : nat) := real_neg (real_of_num x0).
Definition term1007 (x0 : type1551) (x1 : int) (x2 : int) := int_mul (x0 x1 (int_neg x2)) (int_neg x2).
Definition term102 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term230 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term33 := real_of_int (int_of_num (NUMERAL 0)).
Definition term69 (x0 : Prop) := ~ (~ x0).
Definition term34 := real_of_num (NUMERAL 0).
Definition term880 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) -> exists y0 : int, int_lt x0 (int_mul y0 x1).
Definition term832 (x0 : int) (x1 : nat) := or (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))).
Definition term757 (x0 : int) (x1 : nat) (x2 : int) := or (~ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term260 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_neg (real_of_int x1)).
Definition term1108 (x0 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (exists y1 : int, int_lt x0 (int_mul y1 y0)).
Definition term1151 (x0 : int) := fun y0 : int -> int => (fun y1 : int => fun y2 : int -> int => forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ (int_lt y1 (int_mul (y2 y3) y3))) x0 y0.
Definition term941 (x0 : int) := fun y0 : int -> int => (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y3)) \/ (int_lt y1 (int_mul (y2 y3) y3))) x0 y0.
Definition term977 := fun y0 : int => exists y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (forall y2 : int, ~ (int_lt y0 (int_mul y2 y1))).
Definition term463 (x0 : nat) := real_add (real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term57 (x0 : int) := int_le (int_neg x0) (int_of_num (NUMERAL 0)).
Definition term367 (x0 : nat) (x1 : int) := real_ge (real_sub (real_of_num x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term346 (x0 : nat) (x1 : int) (x2 : int) := int_le (int_add (int_mul (int_of_num x0) x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x2 (int_of_num (NUMERAL (BIT1 0)))).
Definition term593 (x0 : int) := fun y0 : nat => (fun y1 : nat => int_le x0 (int_of_num y1)) y0.
Definition term1062 (x0 : type1551) (x1 : int) (x2 : int) := ((int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2)) /\ (~ (int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2))).
Definition term236 (x0 : int) (x1 : int) := int_mul (int_neg x0) x1.
Definition term1109 := fun y0 : int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term890 := fun y0 : int => forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term885 := fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1).
Definition term883 := fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1).
Definition term829 (x0 : int -> nat) (x1 : int) (x2 : int) := ~ (int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2)).
Definition term1079 (x0 : int) := imp ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))).
Definition term519 := forall y0 : nat, exists y1 : nat, Peano.le y0 y1.
Definition term514 := forall y0 : nat, exists y1 : nat, int_le (int_of_num y0) (int_of_num y1).
Definition term129 (x0 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term1112 (x0 : int) (x1 : int) := exists y0 : int, (x1 = (int_of_num (NUMERAL 0))) \/ ((fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term17 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term40 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term725 := fun y0 : int => fun y1 : nat => int_le y0 (int_of_num y1).
Definition term552 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ (Peano.le x0 y0)) x1.
Definition term830 (x0 : int) (x1 : nat) (x2 : int) := (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)).
Definition term1074 (x0 : int) := (~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))) -> int_lt (int_of_num (NUMERAL 0)) x0.
Definition term15 := int_of_num (NUMERAL 0).
Definition term1105 (x0 : int) (x1 : int) := (~ (~ (x1 = (int_of_num (NUMERAL 0))))) \/ (exists y0 : int, int_lt x0 (int_mul y0 x1)).
Definition term373 (x0 : int) (x1 : nat) := real_sub (real_mul (real_of_int x0) (real_of_num x1)).
Definition term13 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term729 (x0 : int) := exists y0 : nat, (fun y1 : int => fun y2 : nat => int_le y1 (int_of_num y2)) x0 y0.
Definition term615 (x0 : int) := exists y0 : nat, (fun y1 : int => fun y2 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (int_le y1 (int_of_num y2))) x0 y0.
Definition term599 (x0 : int) := fun y0 : nat => (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((fun y1 : nat => int_le x0 (int_of_num y1)) y0).
Definition term1052 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (int_lt x2 x3)).
Definition term246 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term469 (x0 : nat) (x1 : int) (x2 : int) := ((~ (~ (((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) /\ (real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)))) /\ (real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))))) -> False) -> ~ (((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) /\ (real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)))) /\ (real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term233 (x0 : int) := ((~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))))))) -> False) -> ~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))))).
Definition term602 := fun y0 : int => exists y1 : nat, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1)).
Definition term1054 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (~ (x0 = x2))) /\ (~ ((~ (x1 = x3)) \/ (int_lt x2 x3))).
Definition term1143 := fun y0 : int => exists y1 : int -> int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2)).
Definition term931 := fun y0 : int => exists y1 : int -> int, forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2)).
Definition term406 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term189 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term410 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term193 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term1042 (x0 : int) (x1 : int) (x2 : int) := (~ (x2 = x0)) \/ (~ (int_lt x1 x2)).
Definition term361 (x0 : nat) (x1 : int) := real_ge (real_sub (real_of_num x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term105 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term1023 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term818 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))) /\ (~ (~ (int_le x1 x2))).
Definition term810 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_le (int_mul x2 x0) (int_mul x2 x1)) \/ ((~ (int_le x0 x1)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2)))).
Definition term119 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term496 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term464 (x0 : nat) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term58 (x0 : int) := real_le (real_of_int (int_neg x0)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term695 := (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> ~ (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term527 := (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term207 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1085 (x0 : type1551) (x1 : int) (x2 : int) := (~ (~ (int_lt (int_of_num (NUMERAL 0)) x2))) -> int_lt x1 (int_mul (x0 x1 x2) x2).
Definition term728 (x0 : int) := fun y0 : nat => (fun y1 : int => fun y2 : nat => int_le y1 (int_of_num y2)) x0 y0.
Definition term614 (x0 : int) := fun y0 : nat => (fun y1 : int => fun y2 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (int_le y1 (int_of_num y2))) x0 y0.
Definition term714 (x0 : int) (x1 : int) := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le x0 y0)) -> int_le (int_mul x1 x0) (int_mul x1 y0).
Definition term424 (x0 : int) (x1 : nat) (x2 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)) (real_of_num (NUMERAL 0))).
Definition term222 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term118 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term143 (x0 : int) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term1009 (x0 : type1551) (x1 : int) (x2 : int) := (~ ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (x0 x1 (int_neg x2)) (int_neg x2)))) -> (int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (x0 x1 (int_neg x2)) (int_neg x2)).
Definition term702 (x0 : int) (x1 : int) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> ~ (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term683 (x0 : int) (x1 : int) := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term575 (x0 : int) := fun y0 : int => (int_le x0 y0) \/ (int_le y0 x0).
Definition term989 (x0 : int) := (fun y0 : int => forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) x0.
Definition term974 (x0 : int) := (fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) x0.
Definition term852 (x0 : int) := (fun y0 : int => forall y1 : int, (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> exists y3 : nat, int_le y2 (int_of_num y3)) -> (forall y2 : int, exists y3 : nat, int_le y2 (int_of_num y3)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : int, int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y2 y0))) -> (forall y2 : int, forall y3 : nat, forall y4 : int, ((int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y3)) /\ (int_le (int_mul (int_of_num y3) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4))) -> int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_le y3 y4)) -> int_le (int_mul y2 y3) (int_mul y2 y4)) -> (forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y2)) -> False) x0.
Definition term643 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) x0.
Definition term483 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1)) x0.
Definition term1067 (x0 : type1551) (x1 : int) (x2 : int) := int_lt x1 (int_mul (x0 x1 (int_neg x2)) (int_neg x2)).
Definition term767 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le x1 x2)).
Definition term177 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term1026 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term474 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term865 := (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term1050 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (int_lt x0 x1)) \/ (int_lt x2 x3).
Definition term1090 (x0 : type1551) (x1 : int) (x2 : int) := ~ (int_lt x1 (int_mul (x0 x1 x2) x2)).
Definition term1035 (x0 : type1551) (x1 : int) (x2 : int) := ~ (int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2)).
Definition term625 (x0 : int -> nat) := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num (x0 y0))).
Definition term971 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (forall y1 : int, ~ (int_lt x0 (int_mul y1 y0))).
Definition term139 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term85 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term520 (x0 : Prop) := (~ x0) -> False.
Definition term1028 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term822 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le x1 x2)))).
Definition term286 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term276 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1))))).
Definition term689 := forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0).
Definition term273 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1031 (x0 : type1551) (x1 : int) (x2 : int) := ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (x0 x1 (int_neg x2)) (int_neg x2))) /\ ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2)).
Definition term107 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term182 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term238 (x0 : int) (x1 : int) := ~ ((int_mul (int_neg x0) x1) = (int_mul x0 (int_neg x1))).
Definition term784 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (int_le y1 y2))) \/ (int_le (int_mul y0 y1) (int_mul y0 y2))) x0.
Definition term1027 (x0 : int) (x1 : int) (x2 : int) := (x1 = x0) /\ (x1 = x2).
Definition term423 (x0 : int) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)))).
Definition term532 := fun y0 : nat => Peano.le y0 y0.
Definition term961 (x0 : int) (x1 : int) := fun y0 : int => ~ (int_lt x0 (int_mul y0 x1)).
Definition term982 (x0 : int) := (~ (~ (x0 = (int_of_num (NUMERAL 0))))) \/ ((int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term22 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term126 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term1107 (x0 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (exists y1 : int, int_lt x0 (int_mul y1 y0)).
Definition term1061 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x2 = x0) /\ ((x3 = x1) /\ (~ (int_lt x0 x1)))) -> ~ (int_lt x2 x3).
Definition term113 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term965 (x0 : int) (x1 : int) := ~ ((~ (x1 = (int_of_num (NUMERAL 0)))) -> exists y0 : int, int_lt x0 (int_mul y0 x1)).
Definition term970 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt x0 (int_mul y2 y1)) y0).
Definition term960 (x0 : int) (x1 : int) := fun y0 : int => ~ ((fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term749 (x0 : int) (x1 : int) := fun y0 : int => ~ ((fun y1 : int => int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x1)) y0).
Definition term142 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term1117 (x0 : int) (x1 : int) := fun y0 : int => (x1 = (int_of_num (NUMERAL 0))) \/ ((fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term956 (x0 : int) (x1 : int) := ~ (exists y0 : int, int_lt x0 (int_mul y0 x1)).
Definition term744 (x0 : int) (x1 : int) := ~ (exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1)).
Definition term1082 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt x1 (int_mul (x0 x1 x2) x2)) \/ (~ (int_lt (int_of_num (NUMERAL 0)) x2)).
Definition term537 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 y0) x1.
Definition term493 (x0 : nat) := forall y0 : nat, (int_le (int_of_num x0) (int_of_num y0)) = (Peano.le x0 y0).
Definition term889 (x0 : int) := forall y0 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (exists y1 : int, int_lt x0 (int_mul y1 y0)).
Definition term584 := forall y0 : int, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term1057 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) /\ (~ (int_lt x1 x2)).
Definition term115 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term45 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term409 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term326 (x0 : nat) (x1 : int) := real_le (real_of_int (int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_mul (int_of_num x0) x1)).
Definition term265 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_mul (int_neg x0) x1)).
Definition term317 (x0 : int) (x1 : nat) (x2 : int) := ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2).
Definition term669 := int_le (int_of_num (NUMERAL (BIT1 0))).
Definition term458 (x0 : int) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_mul (real_of_int x0) (real_of_num x1)).
Definition term432 (x0 : int) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term321 (x0 : int) (x1 : nat) (x2 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2).
Definition term588 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term212 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term335 (x0 : nat) := real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term641 := fun y0 : int => forall y1 : nat, ~ (int_le y0 (int_of_num y1)).
Definition term312 (x0 : int) (x1 : int) := ~ ((real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1)))).
Definition term404 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term403 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term187 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term186 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term75 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term715 (x0 : int) (x1 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le x0 y0)) -> int_le (int_mul x1 x0) (int_mul x1 y0).
Definition term478 (x0 : int) (x1 : nat) := forall y0 : int, ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0).
Definition term264 (x0 : int) (x1 : int) := int_le (int_add (int_mul x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_neg x0) x1).
Definition term651 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term151 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term457 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term261 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1))).
Definition term454 (x0 : int) (x1 : nat) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term329 (x0 : nat) := real_of_int (int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term300 (x0 : int) (x1 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term49 (x0 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term840 (x0 : int) (x1 : nat) := ~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))).
Definition term712 := fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0).
Definition term1000 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x2 = x0) -> (~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))).
Definition term688 := ~ (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term217 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term169 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term1171 (x0 : type1551) (x1 : int) (x2 : int) := @eq Prop ((x2 = (int_of_num (NUMERAL 0))) \/ (int_lt x1 (int_mul (x0 x1 x2) x2))).
Definition term389 (x0 : int) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term878 := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0)).
Definition term522 := ~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1).
Definition term620 (x0 : int -> nat) (x1 : int) := (fun y0 : nat => (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (int_le x1 (int_of_num y0))) (x0 x1).
Definition term141 (x0 : int) := real_ge (real_of_int x0).
Definition term462 (x0 : nat) := real_add (real_add (real_of_num x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term298 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_mul (real_of_int x0) (real_of_int x1))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term272 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term1070 (x0 : type1551) (x1 : int) (x2 : int) := (~ (int_lt x1 (int_mul (x0 x1 (int_neg x2)) (int_neg x2)))) -> ~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x2)).
Definition term813 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_mul x0 x1) (int_mul x0 x2)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le x1 x2))).
Definition term328 (x0 : nat) (x1 : int) := int_mul (int_of_num x0) x1.
Definition term781 (x0 : int) := (fun y0 : int => forall y1 : nat, forall y2 : int, ((~ (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1))) \/ (~ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)))) \/ (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) x0.
Definition term1055 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x0 = x2)) \/ (int_lt x1 x2)).
Definition term843 (x0 : int) (x1 : nat) (x2 : int) := imp (~ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))))).
Definition term697 (x0 : int) (x1 : int) := (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term366 (x0 : int) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term623 (x0 : int -> nat) := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num (x0 y0))).
Definition term886 (x0 : int) := or (~ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term839 (x0 : int) (x1 : nat) (x2 : int) := (~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)))) /\ (~ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term101 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term803 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x2)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (int_le (int_mul x1 x0) (int_mul x1 x2))).
Definition term555 (x0 : Prop) := (~ x0) -> x0.
Definition term1084 (x0 : type1551) (x1 : int) (x2 : int) := @eq Prop ((int_lt x1 (int_mul (x0 x1 x2) x2)) \/ (~ (int_lt (int_of_num (NUMERAL 0)) x2))).
Definition term963 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ (~ (exists y0 : int, int_lt x0 (int_mul y0 x1))).
Definition term56 (x0 : int) := ~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term396 (x0 : int) (x1 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1)).
Definition term461 (x0 : int) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_mul (real_of_int x0) (real_of_num x1))).
Definition term95 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term621 (x0 : int -> nat) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (int_le x1 (int_of_num (x0 x1))).
Definition term1076 (x0 : int) := ~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term343 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term449 (x0 : int) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term431 (x0 : int) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term421 (x0 : int) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term81 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term1021 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term444 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2))).
Definition term147 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))).
Definition term391 (x0 : int) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))).
Definition term204 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term884 (x0 : int) := fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) y0) -> exists y1 : int, int_lt x0 (int_mul y1 y0).
Definition term774 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le x1 x2).
Definition term450 (x0 : int) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term816 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term900 (x0 : int) (x1 : int) := @eq Prop ((~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (exists y0 : int, int_lt x0 (int_mul y0 x1))).
Definition term899 (x0 : int) (x1 : int) := @eq Prop ((~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (exists y0 : int, (fun y1 : int => int_lt x0 (int_mul y1 x1)) y0)).
Definition term596 (x0 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (exists y0 : nat, int_le x0 (int_of_num y0))).
Definition term595 (x0 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (exists y0 : nat, (fun y1 : nat => int_le x0 (int_of_num y1)) y0)).
Definition term554 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term701 (x0 : int) (x1 : int) := (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> ~ (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term882 (x0 : int) := forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, int_lt x0 (int_mul y1 y0).
Definition term248 (x0 : int) (x1 : int) := real_mul (real_of_int (int_neg x0)) (real_of_int x1).
Definition term761 (x0 : int) (x1 : nat) := fun y0 : int => ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0)).
Definition term975 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) x0).
Definition term639 (x0 : int) := ~ ((fun y0 : int => exists y1 : nat, int_le y0 (int_of_num y1)) x0).
Definition term706 (x0 : int) := forall y0 : int, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> exists y2 : nat, int_le y1 (int_of_num y2)) -> (forall y1 : int, exists y2 : nat, int_le y1 (int_of_num y2)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : int, int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x0))) -> (forall y1 : int, forall y2 : nat, forall y3 : int, ((int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y2)) /\ (int_le (int_mul (int_of_num y2) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3))) -> int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_le y2 y3)) -> int_le (int_mul y1 y2) (int_mul y1 y3)) -> ~ (forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y1)).
Definition term705 (x0 : int) := forall y0 : int, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> exists y2 : nat, int_le y1 (int_of_num y2)) -> (forall y1 : int, exists y2 : nat, int_le y1 (int_of_num y2)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : int, int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x0))) -> (forall y1 : int, forall y2 : nat, forall y3 : int, ((int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y2)) /\ (int_le (int_mul (int_of_num y2) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3))) -> int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_le y2 y3)) -> int_le (int_mul y1 y2) (int_mul y1 y3)) -> (forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y1)) -> False.
Definition term99 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term240 (x0 : int) (x1 : int) := int_le (int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 (int_neg x1)).
Definition term604 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term481 (x0 : int) := (fun y0 : int => (int_add (int_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term987 (x0 : type1551) (x1 : int) := fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x1 (int_mul (x0 x1 y0) y0)).
Definition term922 (x0 : int) (x1 : int -> int) (x2 : int) := (fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) x2)) \/ (int_lt x0 (int_mul y0 x2))) (x1 x2).
Definition term802 (x0 : int) := ~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term591 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term1018 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term157 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term662 (x0 : int -> nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_of_num (x0 x1)).
Definition term581 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (exists y0 : nat, int_le x0 (int_of_num y0)).
Definition term833 (x0 : int) (x1 : nat) (x2 : int) := (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term990 (x0 : int) (x1 : int) := (fun y0 : int => (int_mul (int_neg x0) y0) = (int_mul x0 (int_neg y0))) x1.
Definition term758 (x0 : int) (x1 : nat) (x2 : int) := or ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term23 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term694 := (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term206 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term759 (x0 : int) (x1 : nat) (x2 : int) := (~ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)).
Definition term1019 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term1146 := exists y0 : type1551, forall y1 : int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ (int_lt y2 (int_mul (y3 y4) y4))) y1 (y0 y1).
Definition term1142 (x0 : int) := exists y0 : int -> int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul (y0 y1) y1)).
Definition term1123 (x0 : int) := exists y0 : int -> int, forall y1 : int, (fun y2 : int => fun y3 : int => (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y3 y2))) y1 (y0 y1).
Definition term936 := exists y0 : type1551, forall y1 : int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y4)) \/ (int_lt y2 (int_mul (y3 y4) y4))) y1 (y0 y1).
Definition term934 (x0 : type1548) := exists y0 : type1551, forall y1 : int, x0 y1 (y0 y1).
Definition term930 (x0 : int) := exists y0 : int -> int, forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul (y0 y1) y1)).
Definition term911 (x0 : int) := exists y0 : int -> int, forall y1 : int, (fun y2 : int => fun y3 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt x0 (int_mul y3 y2))) y1 (y0 y1).
Definition term909 (x0 : type1550) := exists y0 : int -> int, forall y1 : int, x0 y1 (y0 y1).
Definition term741 := exists y0 : int -> nat, forall y1 : int, int_le y1 (int_of_num (y0 y1)).
Definition term724 := exists y0 : int -> nat, forall y1 : int, (fun y2 : int => fun y3 : nat => int_le y2 (int_of_num y3)) y1 (y0 y1).
Definition term628 := exists y0 : int -> nat, forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (int_le y1 (int_of_num (y0 y1))).
Definition term609 := exists y0 : int -> nat, forall y1 : int, (fun y2 : int => fun y3 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (int_le y2 (int_of_num y3))) y1 (y0 y1).
Definition term607 (x0 : type1552) := exists y0 : int -> nat, forall y1 : int, x0 y1 (y0 y1).
Definition term993 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ~ (int_lt x0 (int_mul y0 x1))) x2.
Definition term2 (x0 : int) := ~ ((int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term1169 (x0 : type1551) (x1 : int) (x2 : int) := (fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x1 (int_mul (x0 x1 y0) y0))) x2.
Definition term438 (x0 : int) (x1 : nat) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_int x2)).
Definition term130 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term241 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_mul x0 (int_neg x1))).
Definition term736 (x0 : int -> nat) := fun y0 : int => int_le y0 (int_of_num (x0 y0)).
Definition term691 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term278 (x0 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term210 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term456 (x0 : int) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term696 (x0 : int) (x1 : int) := imp (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))).
Definition term516 (x0 : nat) := fun y0 : nat => Peano.le x0 y0.
Definition term285 (x0 : int) (x1 : int) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term392 (x0 : int) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term398 (x0 : int) := real_add (real_of_int x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term333 (x0 : nat) := real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term660 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term1045 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (int_lt x0 x1)) \/ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (int_lt x2 x3))).
Definition term835 (x0 : int) (x1 : nat) (x2 : int) := @eq Prop ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ ((~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term405 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term188 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term185 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term112 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term610 := fun y0 : int => fun y1 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1)).
Definition term46 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term342 (x0 : int) (x1 : nat) (x2 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) /\ (real_le (real_mul (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x1) (real_of_int x2))).
Definition term876 (x0 : int) := fun y0 : int => (int_mul (int_neg x0) y0) = (int_mul x0 (int_neg y0)).
Definition term553 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term476 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term345 (x0 : int) (x1 : nat) (x2 : int) := ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)).
Definition term501 (x0 : int) := (fun y0 : int => exists y1 : nat, int_le y0 (int_of_num y1)) x0.
Definition term1106 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (exists y0 : int, int_lt x0 (int_mul y0 x1)).
Definition term869 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term412 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term611 (x0 : int) := (fun y0 : int => fun y1 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1))) x0.
Definition term1129 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => fun y2 : int => (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y2 y1))) x1 y0.
Definition term917 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => fun y2 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul y2 y1))) x1 y0.
Definition term1086 (x0 : int) := ~ (~ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term482 (x0 : int) := int_add (int_of_num (NUMERAL 0)) x0.
Definition term1100 := (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term873 := (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term836 (x0 : int) (x1 : nat) (x2 : int) := @eq Prop ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))))).
Definition term806 (x0 : int) (x1 : int) := or (~ (int_le x0 x1)).
Definition term538 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => Peano.le x0 y0) x1).
Definition term311 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1)))))) -> False) -> ~ ((real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1)))).
Definition term1008 (x0 : type1551) (x1 : int) (x2 : int) := x0 x1 (int_neg x2).
Definition term850 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul x1 x2)) -> False.
Definition term205 := real_le (real_of_num (NUMERAL 0)).
Definition term20 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term213 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term445 (x0 : int) (x1 : nat) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term459 (x0 : int) (x1 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1)).
Definition term1125 (x0 : int) (x1 : int) := (fun y0 : int => fun y1 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0))) x1.
Definition term913 (x0 : int) (x1 : int) := (fun y0 : int => fun y1 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0))) x1.
Definition term38 (x0 : int) := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term645 (x0 : int) (x1 : nat) := (fun y0 : nat => ~ (int_le x0 (int_of_num y0))) x1.
Definition term772 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (int_le x0 x2))) \/ (int_le (int_mul x1 x0) (int_mul x1 x2)).
Definition term964 (x0 : int) (x1 : int) := (~ (x1 = (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ~ (int_lt x0 (int_mul y0 x1))).
Definition term296 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term365 (x0 : nat) (x1 : int) := real_add (real_of_num x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term923 (x0 : int) (x1 : int -> int) (x2 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x2)) \/ (int_lt x0 (int_mul (x1 x2) x2)).
Definition term324 (x0 : int) (x1 : nat) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1).
Definition term114 (x0 : int) := or (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term220 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term648 (x0 : int) := (int_le x0 (int_of_num (NUMERAL 0))) -> ~ (int_le x0 (int_of_num (NUMERAL 0))).
Definition term152 := real_lt (real_of_num (NUMERAL 0)).
Definition term896 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => int_lt x0 (int_mul y0 x1)) x2.
Definition term664 (x0 : int -> nat) (x1 : int) := ~ (int_le x1 (int_of_num (x0 x1))).
Definition term746 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1)) x2.
Definition term1150 (x0 : int) (x1 : int -> int) := (fun y0 : int -> int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul (y0 y1) y1))) x1.
Definition term940 (x0 : int) (x1 : int -> int) := (fun y0 : int -> int => forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul (y0 y1) y1))) x1.
Definition term698 (x0 : int) (x1 : int) := (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> ~ (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term1032 (x0 : type1551) (x1 : int) (x2 : int) := (((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (x0 x1 (int_neg x2)) (int_neg x2))) /\ ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2))) -> (int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2).
Definition term903 (x0 : int) (x1 : int) := fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ ((fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term592 (x0 : int) (x1 : nat) := (fun y0 : nat => int_le x0 (int_of_num y0)) x1.
Definition term674 (x0 : int) (x1 : int) (x2 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul x1 x2).
Definition term635 (x0 : int) := forall y0 : nat, ~ (int_le x0 (int_of_num y0)).
Definition term29 (x0 : int) := real_add (real_of_int x0).
Definition term787 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term509 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term508 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) y0).
Definition term227 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term360 (x0 : nat) (x1 : int) (x2 : int) := ~ (~ (((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) /\ (real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)))) /\ (real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0))))))).
Definition term70 (x0 : int) := ~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0)))))).
Definition term1059 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (int_lt x2 x3)))).
Definition term349 (x0 : nat) (x1 : int) := real_of_int (int_add (int_mul (int_of_num x0) x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term243 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term782 (x0 : int) (x1 : nat) := (fun y0 : nat => forall y1 : int, ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y0))) \/ (~ (int_le (int_mul (int_of_num y0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1))) x1.
Definition term363 (x0 : nat) (x1 : int) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term447 (x0 : int) (x1 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term429 (x0 : int) (x1 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term419 (x0 : int) (x1 : nat) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term743 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term446 (x0 : int) (x1 : nat) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term369 (x0 : int) (x1 : nat) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term229 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term972 (x0 : int) := exists y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) /\ (forall y1 : int, ~ (int_lt x0 (int_mul y1 y0))).
Definition term1002 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term1149 (x0 : int) (x1 : int -> int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2))) x0 x1.
Definition term939 (x0 : int) (x1 : int -> int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2))) x0 x1.
Definition term37 (x0 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term215 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term470 (x0 : nat) (x1 : int) (x2 : int) := ~ (((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) /\ (real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)))) /\ (real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term413 (x0 : int) (x1 : nat) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2).
Definition term551 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term598 (x0 : int) (x1 : nat) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (int_le x0 (int_of_num x1)).
Definition term539 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term996 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) \/ (~ (int_lt x2 x3)).
Definition term181 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term851 (x0 : int -> nat) (x1 : int) (x2 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2)) -> False.
Definition term670 (x0 : int) := int_le (int_of_num (NUMERAL (BIT1 0))) x0.
Definition term25 (x0 : nat) := real_of_int (int_of_num x0).
Definition term513 := fun y0 : nat => exists y1 : nat, int_le (int_of_num y0) (int_of_num y1).
Definition term347 (x0 : nat) (x1 : int) (x2 : int) := real_le (real_of_int (int_add (int_mul (int_of_num x0) x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x2 (int_of_num (NUMERAL (BIT1 0))))).
Definition term1166 (x0 : type1551) (x1 : int) (x2 : int) := (x2 = (int_of_num (NUMERAL 0))) \/ (int_lt x1 (int_mul (x0 x1 x2) x2)).
Definition term9 (x0 : int) := ~ ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term793 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ (int_le x0 x2)) \/ (int_le (int_mul x1 x0) (int_mul x1 x2))).
Definition term162 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term862 := (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term566 := (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False.
Definition term814 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_le x0 x2)))) -> int_le (int_mul x1 x0) (int_mul x1 x2).
Definition term4 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term330 (x0 : nat) := real_mul (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term491 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term490 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term192 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term92 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term1005 (x0 : int) := ~ (x0 = x0).
Definition term132 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term344 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term322 (x0 : int) (x1 : nat) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1).
Definition term1037 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2)) -> ~ (int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2)).
Definition term756 (x0 : int) (x1 : nat) (x2 : int) := (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term1064 (x0 : type1551) (x1 : int) (x2 : int) := ((x1 = x1) /\ (((int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2)) /\ (~ (int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2))))) -> ~ (int_lt x1 (int_mul (x0 x1 (int_neg x2)) (int_neg x2))).
Definition term789 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) x2.
Definition term21 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term549 := fun y0 : nat => forall y1 : nat, ~ (Peano.le y0 y1).
Definition term61 (x0 : int) := real_le (real_of_int (int_neg x0)).
Definition term18 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term183 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1040 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((int_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3)))).
Definition term41 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term387 (x0 : int) (x1 : int) (x2 : nat) := real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x1) (real_of_num x2)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term386 (x0 : int) (x1 : nat) (x2 : int) := real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_num x1) (real_of_int x2)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1134 (x0 : int) (x1 : int -> int) (x2 : int) := (fun y0 : int => (x2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y0 x2))) (x1 x2).
Definition term671 (x0 : int) := imp (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term417 (x0 : int) (x1 : int) (x2 : nat) := and ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x2) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x1) (real_of_num x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x2))) (real_of_num (NUMERAL 0)))).
Definition term748 (x0 : int) (x1 : int) (x2 : int) := ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul x1 x2)).
Definition term791 (x0 : int) (x1 : nat) := ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)).
Definition term293 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term53 (x0 : int) := real_le (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term507 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1).
Definition term893 (x0 : Prop) (x1 : int -> Prop) := exists y0 : int, x0 \/ (x1 y0).
Definition term214 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term96 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term124 := real_sub (real_of_num (NUMERAL 0)).
Definition term280 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term494 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_le (int_of_num x0) (int_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term768 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le x1 x2)).
Definition term471 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term999 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))).
Definition term1128 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => fun y2 : int => (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y2 y1))) x1 y0.
Definition term916 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => fun y2 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul y2 y1))) x1 y0.
Definition term266 (x0 : int) (x1 : int) := int_add (int_mul x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0))).
Definition term525 := (((~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term680 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1).
Definition term150 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term995 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((int_lt x2 x3) = (int_lt x0 x1)) -> (int_lt x0 x1) \/ (~ (int_lt x2 x3)).
Definition term103 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term634 (x0 : int) := fun y0 : nat => ~ (int_le x0 (int_of_num y0)).
Definition term378 (x0 : int) (x1 : nat) := real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term1044 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((int_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3))))).
Definition term294 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))).
Definition term912 (x0 : int) := fun y0 : int => fun y1 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0)).
Definition term1049 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x1 = x3)) \/ ((~ (int_lt x0 x1)) \/ (int_lt x2 x3)).
Definition term271 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term586 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term67 (x0 : int) := and ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term301 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term484 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term866 := (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term270 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))).
Definition term180 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term441 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term395 (x0 : int) (x1 : nat) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term968 (x0 : int) (x1 : int) := (fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, int_lt x0 (int_mul y1 y0)) x1.
Definition term846 (x0 : int -> nat) (x1 : int) (x2 : int) := ((int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) /\ (int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2))) -> int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2).
Definition term796 (x0 : int -> nat) (x1 : int) := ~ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term254 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term489 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term488 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term510 (x0 : nat) := (fun y0 : int => exists y1 : nat, int_le y0 (int_of_num y1)) (int_of_num x0).
Definition term765 := fun y0 : int => forall y1 : nat, forall y2 : int, ((~ (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1))) \/ (~ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)))) \/ (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)).
Definition term722 := fun y0 : int => forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2).
Definition term815 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term563 := ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False.
Definition term414 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_num x1) (real_of_int x2)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term303 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term377 (x0 : int) (x1 : nat) := real_ge (real_sub (real_mul (real_of_num x1) (real_of_int x0)) (real_mul (real_of_num x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term1170 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt x1 (int_mul (x0 x1 x2) x2)) \/ (x2 = (int_of_num (NUMERAL 0))).
Definition term1048 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (int_lt x0 x1)) \/ ((~ (x1 = x3)) \/ (int_lt x2 x3)).
Definition term764 (x0 : int) := forall y0 : nat, forall y1 : int, ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y0))) \/ (~ (int_le (int_mul (int_of_num y0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1)).
Definition term479 (x0 : int) := forall y0 : nat, forall y1 : int, ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y0)) /\ (int_le (int_mul (int_of_num y0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1).
Definition term682 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1)).
Definition term340 (x0 : int) (x1 : nat) := and (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)).
Definition term824 (x0 : int -> nat) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) /\ (int_le (int_of_num (NUMERAL (BIT1 0))) x2).
Definition term812 (x0 : int) (x1 : int) (x2 : int) := or (int_le (int_mul x1 x0) (int_mul x1 x2)).
Definition term32 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term585 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term297 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_add (real_mul (real_of_int x0) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term436 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2))) (real_of_num (NUMERAL 0)).
Definition term379 (x0 : int) (x1 : nat) := real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term1155 := @eq Prop (forall y0 : int, exists y1 : int -> int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2))).
Definition term1154 := @eq Prop (forall y0 : int, exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ (int_lt y2 (int_mul (y3 y4) y4))) y0 y1).
Definition term1132 (x0 : int) := @eq Prop (forall y0 : int, exists y1 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0))).
Definition term1131 (x0 : int) := @eq Prop (forall y0 : int, exists y1 : int, (fun y2 : int => fun y3 : int => (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y3 y2))) y0 y1).
Definition term945 := @eq Prop (forall y0 : int, exists y1 : int -> int, forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2))).
Definition term944 := @eq Prop (forall y0 : int, exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y4)) \/ (int_lt y2 (int_mul (y3 y4) y4))) y0 y1).
Definition term920 (x0 : int) := @eq Prop (forall y0 : int, exists y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0))).
Definition term919 (x0 : int) := @eq Prop (forall y0 : int, exists y1 : int, (fun y2 : int => fun y3 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt x0 (int_mul y3 y2))) y0 y1).
Definition term732 := @eq Prop (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term731 := @eq Prop (forall y0 : int, exists y1 : nat, (fun y2 : int => fun y3 : nat => int_le y2 (int_of_num y3)) y0 y1).
Definition term618 := @eq Prop (forall y0 : int, exists y1 : nat, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1))).
Definition term617 := @eq Prop (forall y0 : int, exists y1 : nat, (fun y2 : int => fun y3 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (int_le y2 (int_of_num y3))) y0 y1).
Definition term117 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term1148 (x0 : int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2))) x0.
Definition term938 (x0 : int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2))) x0.
Definition term754 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL (BIT1 0))) x1) /\ (forall y0 : int, ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))).
Definition term93 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term292 (x0 : int) (x1 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term1147 := fun y0 : int => fun y1 : int -> int => forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2)).
Definition term937 := fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2)).
Definition term742 (x0 : int -> Prop) := ~ (ex x0).
Definition term533 (x0 : nat -> Prop) := ~ (ex x0).
Definition term1158 (x0 : type1551) (x1 : int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x1 (int_mul (x0 x1 y0) y0)).
Definition term1139 (x0 : int) (x1 : int -> int) := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul (x1 y0) y0)).
Definition term834 (x0 : int) (x1 : nat) (x2 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term826 (x0 : int -> nat) (x1 : int) := int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term36 (x0 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term382 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_num x1) (real_of_int x2)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term370 (x0 : int) (x1 : nat) := real_ge (real_sub (real_mul (real_of_num x1) (real_of_int x0)) (real_mul (real_of_num x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term304 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term277 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term590 (x0 : int) := exists y0 : nat, (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((fun y1 : nat => int_le x0 (int_of_num y1)) y0).
Definition term258 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int (int_neg x1)).
Definition term167 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term122 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term966 (x0 : int) := ~ (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, int_lt x0 (int_mul y1 y0)).
Definition term825 (x0 : int -> nat) (x1 : int) (x2 : int) := ((int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) /\ (int_le (int_of_num (NUMERAL (BIT1 0))) x2)) -> int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2).
Definition term500 := fun y0 : int => exists y1 : nat, int_le y0 (int_of_num y1).
Definition term809 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ ((~ (int_le x0 x2)) \/ (int_le (int_mul x1 x0) (int_mul x1 x2)))).
Definition term546 (x0 : nat) := (fun y0 : nat => exists y1 : nat, Peano.le y0 y1) x0.
Definition term235 (x0 : int) (x1 : int) := ~ (~ ((int_mul (int_neg x0) x1) = (int_mul x0 (int_neg x1)))).
Definition term253 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term804 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (int_le (int_mul x1 x0) (int_mul x1 x2)).
Definition term1089 (x0 : type1551) (x1 : int) (x2 : int) := (~ (int_lt x1 (int_mul (x0 x1 x2) x2))) -> int_lt x1 (int_mul (x0 x1 x2) x2).
Definition term178 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term794 (x0 : int -> nat) (x1 : int) := int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term1073 (x0 : int) := @eq Prop ((x0 = (int_of_num (NUMERAL 0))) \/ ((int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))).
Definition term1017 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term678 (x0 : int) (x1 : int) := exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1).
Definition term136 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term135 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term175 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term165 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term905 (x0 : int) (x1 : int) := exists y0 : int, (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (int_lt x0 (int_mul y0 x1)).
Definition term848 (x0 : int -> nat) (x1 : int) (x2 : int) := (~ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2))) -> int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2).
Definition term898 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => int_lt x0 (int_mul y1 x1)) y0.
Definition term116 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term1152 (x0 : int) := exists y0 : int -> int, (fun y1 : int => fun y2 : int -> int => forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ (int_lt y1 (int_mul (y2 y3) y3))) x0 y0.
Definition term942 (x0 : int) := exists y0 : int -> int, (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y3)) \/ (int_lt y1 (int_mul (y2 y3) y3))) x0 y0.
Definition term578 (x0 : int) (x1 : nat) := int_le x0 (int_of_num x1).
Definition term798 (x0 : int -> nat) (x1 : int) := x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))).
Definition term487 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term48 (x0 : int) := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term827 (x0 : int -> nat) (x1 : int) (x2 : int) := int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2).
Definition term384 (x0 : int) (x1 : nat) := real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term97 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term601 (x0 : int) := exists y0 : nat, (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (int_le x0 (int_of_num y0)).
Definition term811 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2)).
Definition term687 := (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term1020 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term371 (x0 : int) (x1 : nat) := real_mul (real_of_int x0) (real_of_num x1).
Definition term477 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term534 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term443 (x0 : int) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term110 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term1133 (x0 : int) (x1 : int -> int) (x2 : int) := (fun y0 : int => fun y1 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0))) x2 (x1 x2).
Definition term921 (x0 : int) (x1 : int -> int) (x2 : int) := (fun y0 : int => fun y1 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0))) x2 (x1 x2).
Definition term1075 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term226 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term502 (x0 : int) := exists y0 : nat, int_le x0 (int_of_num y0).
Definition term1036 (x0 : type1551) (x1 : int) (x2 : int) := int_neg (x0 x1 (int_neg x2)).
Definition term1162 (x0 : type1551) := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (x0 y0 y1) y1)).
Definition term1110 := forall y0 : int, forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term952 (x0 : type1551) := forall y0 : int, forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt y0 (int_mul (x0 y0 y1) y1)).
Definition term891 := forall y0 : int, forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term855 := forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1).
Definition term780 := forall y0 : int, forall y1 : int, forall y2 : int, ((~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (~ (int_le y1 y2))) \/ (int_le (int_mul y0 y1) (int_mul y0 y2)).
Definition term778 (x0 : int) := forall y0 : int, forall y1 : int, ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le y0 y1))) \/ (int_le (int_mul x0 y0) (int_mul x0 y1)).
Definition term766 := forall y0 : int, forall y1 : nat, forall y2 : int, ((~ (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1))) \/ (~ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)))) \/ (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)).
Definition term719 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2).
Definition term717 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le y0 y1)) -> int_le (int_mul x0 y0) (int_mul x0 y1).
Definition term710 := forall y0 : int, forall y1 : int, (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> exists y3 : nat, int_le y2 (int_of_num y3)) -> (forall y2 : int, exists y3 : nat, int_le y2 (int_of_num y3)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : int, int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y2 y0))) -> (forall y2 : int, forall y3 : nat, forall y4 : int, ((int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y3)) /\ (int_le (int_mul (int_of_num y3) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4))) -> int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_le y3 y4)) -> int_le (int_mul y2 y3) (int_mul y2 y4)) -> ~ (forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y2)).
Definition term709 := forall y0 : int, forall y1 : int, (forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> exists y3 : nat, int_le y2 (int_of_num y3)) -> (forall y2 : int, exists y3 : nat, int_le y2 (int_of_num y3)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : int, int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y2 y0))) -> (forall y2 : int, forall y3 : nat, forall y4 : int, ((int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y3)) /\ (int_le (int_mul (int_of_num y3) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4))) -> int_le (int_add y2 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y3) y4)) -> (forall y2 : int, forall y3 : int, forall y4 : int, ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_le y3 y4)) -> int_le (int_mul y2 y3) (int_mul y2 y4)) -> (forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y2)) -> False.
Definition term667 := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1).
Definition term568 := forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0).
Definition term480 := forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2).
Definition term314 := forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1)).
Definition term1138 (x0 : int) (x1 : int -> int) := forall y0 : int, (fun y1 : int => fun y2 : int => (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y2 y1))) y0 (x1 y0).
Definition term926 (x0 : int) (x1 : int -> int) := forall y0 : int, (fun y1 : int => fun y2 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul y2 y1))) y0 (x1 y0).
Definition term89 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term202 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term55 (x0 : int) := real_le (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term426 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2))) (real_of_num (NUMERAL 0)).
Definition term224 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term1124 (x0 : int) := fun y0 : int => fun y1 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0)).
Definition term984 := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))).
Definition term111 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term201 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)).
Definition term159 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term337 (x0 : nat) (x1 : int) := real_mul (real_of_int (int_of_num x0)) (real_of_int x1).
Definition term1163 := fun y0 : type1551 => forall y1 : int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ (int_lt y2 (int_mul (y3 y4) y4))) y1 (y0 y1).
Definition term1141 (x0 : int) := fun y0 : int -> int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul (y0 y1) y1)).
Definition term1140 (x0 : int) := fun y0 : int -> int => forall y1 : int, (fun y2 : int => fun y3 : int => (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y3 y2))) y1 (y0 y1).
Definition term953 := fun y0 : type1551 => forall y1 : int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y4)) \/ (int_lt y2 (int_mul (y3 y4) y4))) y1 (y0 y1).
Definition term929 (x0 : int) := fun y0 : int -> int => forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul (y0 y1) y1)).
Definition term928 (x0 : int) := fun y0 : int -> int => forall y1 : int, (fun y2 : int => fun y3 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt x0 (int_mul y3 y2))) y1 (y0 y1).
Definition term740 := fun y0 : int -> nat => forall y1 : int, int_le y1 (int_of_num (y0 y1)).
Definition term739 := fun y0 : int -> nat => forall y1 : int, (fun y2 : int => fun y3 : nat => int_le y2 (int_of_num y3)) y1 (y0 y1).
Definition term627 := fun y0 : int -> nat => forall y1 : int, (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (int_le y1 (int_of_num (y0 y1))).
Definition term626 := fun y0 : int -> nat => forall y1 : int, (fun y2 : int => fun y3 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (int_le y2 (int_of_num y3))) y1 (y0 y1).
Definition term209 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term339 (x0 : nat) (x1 : int) := real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)).
Definition term613 (x0 : int) (x1 : nat) := (fun y0 : nat => (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (int_le x0 (int_of_num y0))) x1.
Definition term574 (x0 : int) (x1 : int) := (int_le x1 x0) \/ (int_le x0 x1).
Definition term19 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term1161 (x0 : type1551) := forall y0 : int, (fun y1 : int => fun y2 : int -> int => forall y3 : int, (y3 = (int_of_num (NUMERAL 0))) \/ (int_lt y1 (int_mul (y2 y3) y3))) y0 (x0 y0).
Definition term951 (x0 : type1551) := forall y0 : int, (fun y1 : int => fun y2 : int -> int => forall y3 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y3)) \/ (int_lt y1 (int_mul (y2 y3) y3))) y0 (x0 y0).
Definition term737 (x0 : int -> nat) := forall y0 : int, (fun y1 : int => fun y2 : nat => int_le y1 (int_of_num y2)) y0 (x0 y0).
Definition term624 (x0 : int -> nat) := forall y0 : int, (fun y1 : int => fun y2 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y1)) \/ (int_le y1 (int_of_num y2))) y0 (x0 y0).
Definition term174 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term144 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term158 := S (Nat.add 0 0).
Definition term512 := fun y0 : nat => (fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) (int_of_num y0).
Definition term82 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) \/ (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term892 (x0 : Prop) (x1 : int -> Prop) := x0 \/ (exists y0 : int, x1 y0).
Definition term332 (x0 : nat) := real_mul (real_of_num x0).
Definition term771 (x0 : int) (x1 : int) (x2 : int) := or ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le x1 x2))).
Definition term677 (x0 : int) (x1 : int) := exists y0 : int, int_lt x0 (int_mul y0 x1).
Definition term338 (x0 : nat) (x1 : int) := real_mul (real_of_num x0) (real_of_int x1).
Definition term76 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term140 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))).
Definition term807 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ ((int_le (int_mul x2 x0) (int_mul x2 x1)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2))).
Definition term249 (x0 : int) := real_mul (real_of_int (int_neg x0)).
Definition term800 (x0 : int -> nat) (x1 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term856 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> False.
Definition term560 := (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> False.
Definition term521 := (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> False.
Definition term542 (x0 : nat) := forall y0 : nat, ~ (Peano.le x0 y0).
Definition term84 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term948 (x0 : type1551) (x1 : int) := forall y0 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x1 (int_mul (x0 x1 y0) y0)).
Definition term927 (x0 : int) (x1 : int -> int) := forall y0 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul (x1 y0) y0)).
Definition term439 (x0 : nat) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_of_num x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_int x1).
Definition term1046 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x0 = x2)) \/ ((~ (int_lt x0 x1)) \/ ((~ (x1 = x3)) \/ (int_lt x2 x3))).
Definition term357 (x0 : int) (x1 : nat) (x2 : int) := and ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term1051 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (int_lt x0 x1)))) -> ~ (int_lt x2 x3).
Definition term548 := fun y0 : nat => ~ ((fun y1 : nat => exists y2 : nat, Peano.le y1 y2) y0).
Definition term309 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term985 := forall y0 : int, (y0 = (int_of_num (NUMERAL 0))) \/ ((int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))).
Definition term1033 (x0 : type1551) (x1 : int) (x2 : int) := (~ ((int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2))) -> (int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2).
Definition term769 (x0 : int) (x1 : int) (x2 : int) := int_le (int_mul x1 x0) (int_mul x1 x2).
Definition term577 := fun y0 : int => forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0).
Definition term362 (x0 : nat) (x1 : int) := real_sub (real_of_num x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term887 (x0 : int) (x1 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (exists y0 : int, int_lt x0 (int_mul y0 x1)).
Definition term284 (x0 : int) (x1 : int) := real_sub (real_mul (real_of_int x0) (real_neg (real_of_int x1))).
Definition term168 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term579 (x0 : int) := fun y0 : nat => int_le x0 (int_of_num y0).
Definition term647 (x0 : int) := ~ (int_le x0 (int_of_num (NUMERAL 0))).
Definition term959 (x0 : int) (x1 : int) (x2 : int) := ~ (int_lt x0 (int_mul x1 x2)).
Definition term452 (x0 : int) (x1 : nat) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term381 (x0 : int) (x1 : int) (x2 : nat) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x2) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x1) (real_of_num x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x2))) (real_of_num (NUMERAL 0))).
Definition term164 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term1083 (x0 : type1551) (x1 : int) (x2 : int) := @eq Prop ((~ (int_lt (int_of_num (NUMERAL 0)) x2)) \/ (int_lt x1 (int_mul (x0 x1 x2) x2))).
Definition term307 (x0 : int) (x1 : int) := real_ge (real_sub (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term1003 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) -> ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term573 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> ~ (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)).
Definition term1016 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term225 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term902 (x0 : int) (x1 : int) (x2 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x2)) \/ (int_lt x0 (int_mul x1 x2)).
Definition term306 (x0 : int) (x1 : int) := real_sub (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1034 (x0 : type1551) (x1 : int) (x2 : int) := ~ ((int_mul (x0 x1 (int_neg x2)) (int_neg x2)) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2)).
Definition term594 (x0 : int) := exists y0 : nat, (fun y1 : nat => int_le x0 (int_of_num y1)) y0.
Definition term39 (x0 : int) := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term808 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_mul x2 x0) (int_mul x2 x1)) \/ ((~ (int_le x0 x1)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2))).
Definition term451 (x0 : int) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term433 (x0 : int) (x1 : nat) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term194 := real_mul (real_of_num (NUMERAL 0)).
Definition term400 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term819 (x0 : int) := and (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term472 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term350 (x0 : nat) (x1 : int) := real_add (real_of_int (int_mul (int_of_num x0) x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term244 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul (int_neg x0) x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term958 (x0 : int) (x1 : int) (x2 : int) := ~ ((fun y0 : int => int_lt x0 (int_mul y0 x1)) x2).
Definition term747 (x0 : int) (x1 : int) (x2 : int) := ~ ((fun y0 : int => int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1)) x2).
Definition term983 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ ((int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term797 (x0 : int -> nat) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term1025 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term279 (x0 : int) (x1 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1).
Definition term71 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term10 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term506 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) y0.
Definition term31 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term131 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term134 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term52 (x0 : int) := int_le x0 (int_of_num (NUMERAL 0)).
Definition term376 (x0 : int) (x1 : nat) := real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term1096 := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term861 := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term686 (x0 : int) (x1 : int) := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False) -> ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term1066 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt x1 (int_mul (x0 x1 (int_neg x2)) (int_neg x2))) -> ~ (int_lt x1 (int_mul (x0 x1 (int_neg x2)) (int_neg x2))).
Definition term515 (x0 : nat) := fun y0 : nat => int_le (int_of_num x0) (int_of_num y0).
Definition term863 := ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term857 := ~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term567 := ~ (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)).
Definition term561 := ~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term106 (x0 : int) := real_sub (real_of_int x0).
Definition term711 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term87 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term565 := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False) -> ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False.
Definition term760 (x0 : int) (x1 : nat) (x2 : int) := ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)).
Definition term348 (x0 : nat) (x1 : int) := int_add (int_mul (int_of_num x0) x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term242 (x0 : int) (x1 : int) := int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term763 (x0 : int) := fun y0 : nat => forall y1 : int, ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y0))) \/ (~ (int_le (int_mul (int_of_num y0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1)).
Definition term721 (x0 : int) := fun y0 : nat => forall y1 : int, ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y0)) /\ (int_le (int_mul (int_of_num y0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y0) y1).
Definition term466 (x0 : nat) := real_add (real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0))).
Definition term137 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term655 (x0 : int -> nat) (x1 : int) := (int_le x1 (int_of_num (x0 x1))) \/ (~ (int_le (int_of_num (NUMERAL 0)) x1)).
Definition term881 (x0 : int) := fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, int_lt x0 (int_mul y1 y0).
Definition term196 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term994 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term557 (x0 : nat) := (Peano.le x0 x0) -> False.
Definition term66 (x0 : int) := (real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term47 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term576 (x0 : int) := forall y0 : int, (int_le x0 y0) \/ (int_le y0 x0).
Definition term60 (x0 : int) := real_neg (real_of_int x0).
Definition term969 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (~ (y0 = (int_of_num (NUMERAL 0)))) -> exists y1 : int, int_lt x0 (int_mul y1 y0)) x1).
Definition term1097 := imp (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term870 := imp (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)).
Definition term699 := imp (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term693 := imp (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)).
Definition term690 := imp (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)).
Definition term440 (x0 : int) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term78 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term1012 (x0 : type1551) (x1 : int) (x2 : int) := ~ ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2)).
Definition term1116 (x0 : int) (x1 : int) (x2 : int) := (x2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul x1 x2)).
Definition term1157 (x0 : type1551) (x1 : int) := (fun y0 : int -> int => forall y1 : int, (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x1 (int_mul (y0 y1) y1))) (x0 x1).
Definition term947 (x0 : type1551) (x1 : int) := (fun y0 : int -> int => forall y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x1 (int_mul (y0 y1) y1))) (x0 x1).
Definition term1077 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term305 (x0 : int) (x1 : int) := real_sub (real_mul (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term65 (x0 : int) := and (real_le (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term838 (x0 : int) (x1 : nat) (x2 : int) := ~ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)))).
Definition term68 (x0 : int) := ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0)))).
Definition term453 (x0 : int) (x1 : nat) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term448 (x0 : int) (x1 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term435 (x0 : int) (x1 : nat) (x2 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2))) (real_of_num (NUMERAL 0)).
Definition term430 (x0 : int) (x1 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term425 (x0 : int) (x1 : nat) (x2 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2))) (real_of_num (NUMERAL 0)).
Definition term420 (x0 : int) (x1 : nat) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term228 (x0 : int) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term223 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term218 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term170 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term547 (x0 : nat) := ~ ((fun y0 : nat => exists y1 : nat, Peano.le y0 y1) x0).
Definition term325 (x0 : nat) (x1 : int) := int_le (int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x0) x1).
Definition term1136 (x0 : int) (x1 : int -> int) := fun y0 : int => (fun y1 : int => fun y2 : int => (y1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y2 y1))) y0 (x1 y0).
Definition term924 (x0 : int) (x1 : int -> int) := fun y0 : int => (fun y1 : int => fun y2 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y1)) \/ (int_lt x0 (int_mul y2 y1))) y0 (x1 y0).
Definition term820 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term752 (x0 : int) := and (int_le (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term1118 (x0 : int) (x1 : int) := fun y0 : int => (x1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y0 x1)).
Definition term145 (x0 : int) := and ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term1071 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)) -> ~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term341 (x0 : int) (x1 : nat) := and (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term897 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => int_lt x0 (int_mul y1 x1)) y0.
Definition term805 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_mul x2 x0) (int_mul x2 x1)) \/ (~ (int_le (int_of_num (NUMERAL 0)) x2)).
Definition term128 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term776 (x0 : int) (x1 : int) := forall y0 : int, ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_le x0 y0))) \/ (int_le (int_mul x1 x0) (int_mul x1 y0)).
Definition term762 (x0 : int) (x1 : nat) := forall y0 : int, ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0)).
Definition term109 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term505 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> exists y0 : nat, int_le x0 (int_of_num y0).
Definition term94 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term630 (x0 : int) := forall y0 : nat, ~ ((fun y1 : nat => int_le x0 (int_of_num y1)) y0).
Definition term536 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => Peano.le x0 y1) y0).
Definition term600 (x0 : int) := fun y0 : nat => (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (int_le x0 (int_of_num y0)).
Definition term841 (x0 : int) (x1 : nat) := and (~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)))).
Definition term1127 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (x1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y0 x1))) x2.
Definition term356 (x0 : nat) (x1 : int) (x2 : int) := real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))).
Definition term251 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_int x0)) (real_of_int x1).
Definition term1081 (x0 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x0)) -> int_lt (int_of_num (NUMERAL 0)) x0.
Definition term428 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2))).
Definition term16 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term492 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_le (int_of_num y0) (int_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term879 (x0 : int) := imp (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term1172 (x0 : type1551) (x1 : int) (x2 : int) := (~ (x2 = (int_of_num (NUMERAL 0)))) -> int_lt x1 (int_mul (x0 x1 x2) x2).
Definition term133 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term368 (x0 : int) (x1 : nat) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term231 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term104 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term659 (x0 : int -> nat) (x1 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> int_le x1 (int_of_num (x0 x1)).
Definition term1135 (x0 : int) (x1 : int -> int) (x2 : int) := (x2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul (x1 x2) x2)).
Definition term418 (x0 : int) (x1 : nat) (x2 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)) (real_of_num (NUMERAL 0))).
Definition term992 (x0 : type1551) (x1 : int) (x2 : int) := (fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x1 (int_mul (x0 x1 y0) y0))) x2.
Definition term915 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (int_lt x0 (int_mul y0 x1))) x2.
Definition term504 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => exists y1 : nat, int_le y0 (int_of_num y1)) x0.
Definition term364 (x0 : nat) := real_add (real_of_num x0).
Definition term465 (x0 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term331 (x0 : nat) := real_mul (real_of_int (int_of_num x0)).
Definition term35 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term486 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term288 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term962 (x0 : int) (x1 : int) := forall y0 : int, ~ (int_lt x0 (int_mul y0 x1)).
Definition term1153 := fun y0 : int => exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ (int_lt y2 (int_mul (y3 y4) y4))) y0 y1.
Definition term943 := fun y0 : int => exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y4)) \/ (int_lt y2 (int_mul (y3 y4) y4))) y0 y1.
Definition term727 (x0 : int) (x1 : nat) := (fun y0 : int => fun y1 : nat => int_le y0 (int_of_num y1)) x0 x1.
Definition term612 (x0 : int) (x1 : nat) := (fun y0 : int => fun y1 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1))) x0 x1.
Definition term282 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term894 (x0 : int) (x1 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (exists y0 : int, (fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term540 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => Peano.le x0 y1) y0).
Definition term1099 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term872 := (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term176 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term166 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term1103 := (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term1102 := (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term1165 := exists y0 : type1551, forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y1 (int_mul (y0 y1 y2) y2)).
Definition term955 := exists y0 : type1551, forall y1 : int, forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y1 (int_mul (y0 y1 y2) y2)).
Definition term755 (x0 : int) (x1 : nat) (x2 : int) := ~ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term849 (x0 : int -> nat) (x1 : int) (x2 : int) := ~ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2)).
Definition term792 (x0 : nat) (x1 : int) := ~ (int_le (int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x0) x1)).
Definition term751 (x0 : int) (x1 : int) := forall y0 : int, ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1)).
Definition term1053 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (int_lt x2 x3))).
Definition term925 (x0 : int) (x1 : int -> int) := fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul (x1 y0) y0)).
Definition term237 (x0 : int) (x1 : int) := int_mul x0 (int_neg x1).
Definition term90 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term562 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)) -> False.
Definition term837 (x0 : int) (x1 : nat) (x2 : int) := (~ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2).
Definition term98 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term1022 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term817 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (~ (int_le x1 x2))).
Definition term161 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term394 (x0 : int) (x1 : int) (x2 : nat) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x1) (real_of_num x2))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term27 := real_of_num (NUMERAL (BIT1 0)).
Definition term160 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term380 (x0 : int) (x1 : nat) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term121 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term700 (x0 : int) (x1 : int) := (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term295 (x0 : int) (x1 : int) := real_add (real_mul (real_of_int x0) (real_of_int x1)).
Definition term1060 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := imp ((x0 = x2) /\ ((x1 = x3) /\ (~ (int_lt x2 x3)))).
Definition term359 (x0 : nat) (x1 : int) (x2 : int) := ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) /\ (real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)))) /\ (real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0))))).
Definition term1 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term646 (x0 : int -> nat) (x1 : int) := (fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num (x0 y0)))) x1.
Definition term1043 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3))))).
Definition term589 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ (exists y0 : nat, (fun y1 : nat => int_le x0 (int_of_num y1)) y0).
Definition term545 := exists y0 : nat, ~ ((fun y1 : nat => exists y2 : nat, Peano.le y1 y2) y0).
Definition term665 (x0 : int) (x1 : nat) := (int_le x0 (int_of_num x1)) -> False.
Definition term1119 (x0 : int) (x1 : int) := exists y0 : int, (x1 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y0 x1)).
Definition term334 (x0 : nat) := real_le (real_of_int (int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))))).
Definition term200 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term262 (x0 : int) (x1 : int) := or (int_le (int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 (int_neg x1))).
Definition term529 := forall y0 : nat, Peano.le y0 y0.
Definition term571 := (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))) -> ~ (forall y0 : int, forall y1 : int, (int_le y0 y1) \/ (int_le y1 y0)).
Definition term531 := (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> ~ (forall y0 : nat, Peano.le y0 y0).
Definition term351 (x0 : nat) (x1 : int) := real_add (real_of_int (int_mul (int_of_num x0) x1)).
Definition term252 (x0 : int) (x1 : int) := real_add (real_of_int (int_mul (int_neg x0) x1)).
Definition term1072 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) \/ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term316 (x0 : int) (x1 : nat) (x2 : int) := ~ (~ (((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term734 (x0 : int -> nat) (x1 : int) := (fun y0 : nat => int_le x1 (int_of_num y0)) (x0 x1).
Definition term979 (x0 : int) := ~ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term663 (x0 : int -> nat) (x1 : int) := (~ (int_le x1 (int_of_num (x0 x1)))) -> int_le x1 (int_of_num (x0 x1)).
Definition term1041 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3)))).
Definition term374 (x0 : int) (x1 : nat) := real_sub (real_mul (real_of_num x1) (real_of_int x0)) (real_mul (real_of_num x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term51 (x0 : int) := ~ (int_lt (int_of_num (NUMERAL 0)) x0).
Definition term173 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term172 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term692 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> ~ (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)).
Definition term320 (x0 : int) (x1 : nat) (x2 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)).
Definition term844 (x0 : int) (x1 : nat) (x2 : int) := imp ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term788 (x0 : int -> nat) (x1 : int) := (fun y0 : int => int_le y0 (int_of_num (x0 y0))) x1.
Definition term1004 (x0 : int) := (~ (x0 = x0)) -> x0 = x0.
Definition term5 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) (int_neg x0).
Definition term498 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) y0.
Definition term399 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term1069 (x0 : type1551) (x1 : int) (x2 : int) := int_lt x1 (int_mul (x0 x1 x2) x2).
Definition term336 (x0 : nat) (x1 : int) := real_of_int (int_mul (int_of_num x0) x1).
Definition term247 (x0 : int) (x1 : int) := real_of_int (int_mul (int_neg x0) x1).
Definition term998 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term401 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term1038 (x0 : type1551) (x1 : int) (x2 : int) := int_lt x1 (int_mul (int_neg (x0 x1 (int_neg x2))) x2).
Definition term460 (x0 : int) (x1 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_int x0) (real_of_num x1)).
Definition term750 (x0 : int) (x1 : int) := fun y0 : int => ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1)).
Definition term668 := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term666 (x0 : int -> nat) (x1 : int) := (int_le x1 (int_of_num (x0 x1))) -> False.
Definition term415 (x0 : int) (x1 : nat) (x2 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)).
Definition term485 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0)) x1.
Definition term644 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) \/ (int_le y0 x0)) x1.
Definition term473 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term1111 (x0 : int) (x1 : int) := (x1 = (int_of_num (NUMERAL 0))) \/ (exists y0 : int, (fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term100 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : int) := and (~ (int_lt (int_of_num (NUMERAL 0)) x0)).
Definition term786 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_le x0 y0))) \/ (int_le (int_mul x1 x0) (int_mul x1 y0))) x2.
Definition term208 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term155 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term393 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1010 (x0 : type1551) (x1 : int) (x2 : int) := ~ ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (x0 x1 (int_neg x2)) (int_neg x2))).
Definition term442 (x0 : nat) := real_add (real_of_num (NUMERAL 0)) (real_add (real_of_num x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term467 (x0 : int) (x1 : nat) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)))).
Definition term753 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL (BIT1 0))) x1) /\ (~ (exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))).
Definition term511 (x0 : nat) := exists y0 : nat, int_le (int_of_num x0) (int_of_num y0).
Definition term437 (x0 : int) (x1 : nat) (x2 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)).
Definition term831 (x0 : int) (x1 : nat) (x2 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term986 (x0 : type1551) (x1 : int) (x2 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x2)) \/ (int_lt x1 (int_mul (x0 x1 x2) x2)).
Definition term1137 (x0 : int) (x1 : int -> int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul (x1 y0) y0)).
Definition term245 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term828 (x0 : int -> nat) (x1 : int) (x2 : int) := (~ (int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2))) -> int_le (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) x2).
Definition term383 (x0 : int) (x1 : nat) := real_add (real_mul (real_of_int x0) (real_of_num x1)).
Definition term127 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term720 (x0 : int) (x1 : nat) := fun y0 : int => ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0).
Definition term179 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term901 (x0 : int) (x1 : int) (x2 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ ((fun y0 : int => int_lt x0 (int_mul y0 x1)) x2).
Definition term59 (x0 : int) := real_of_int (int_neg x0).
Definition term1156 (x0 : type1551) (x1 : int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2))) x1 (x0 x1).
Definition term946 (x0 : type1551) (x1 : int) := (fun y0 : int => fun y1 : int -> int => forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2))) x1 (x0 x1).
Definition term733 (x0 : int -> nat) (x1 : int) := (fun y0 : int => fun y1 : nat => int_le y0 (int_of_num y1)) x1 (x0 x1).
Definition term619 (x0 : int -> nat) (x1 : int) := (fun y0 : int => fun y1 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1))) x1 (x0 x1).
Definition term138 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term1047 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x2)) \/ (int_lt x1 x2).
Definition term221 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term495 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term773 (x0 : int) (x1 : int) (x2 : int) := ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_le x0 x2))) \/ (int_le (int_mul x1 x0) (int_mul x1 x2)).
Definition term26 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term1101 := (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term874 := (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term375 (x0 : int) (x1 : nat) := real_sub (real_mul (real_of_int x0) (real_of_num x1)) (real_of_num x1).
Definition term427 (x0 : int) (x1 : nat) (x2 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)).
Definition term123 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term1029 (x0 : int) (x1 : int) (x2 : int) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term385 (x0 : int) := real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term274 (x0 : int) (x1 : int) := real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1)).
Definition term54 (x0 : int) := real_le (real_of_int x0).
Definition term88 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term795 (x0 : int -> nat) (x1 : int) := (~ (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))))) -> int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term1145 := forall y0 : int, exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (y4 = (int_of_num (NUMERAL 0))) \/ (int_lt y2 (int_mul (y3 y4) y4))) y0 y1.
Definition term1144 := forall y0 : int, exists y1 : int -> int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y0 (int_mul (y1 y2) y2)).
Definition term1122 (x0 : int) := forall y0 : int, exists y1 : int, (fun y2 : int => fun y3 : int => (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y3 y2))) y0 y1.
Definition term1121 (x0 : int) := forall y0 : int, exists y1 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0)).
Definition term935 := forall y0 : int, exists y1 : int -> int, (fun y2 : int => fun y3 : int -> int => forall y4 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y4)) \/ (int_lt y2 (int_mul (y3 y4) y4))) y0 y1.
Definition term933 (x0 : type1548) := forall y0 : int, exists y1 : int -> int, x0 y0 y1.
Definition term932 := forall y0 : int, exists y1 : int -> int, forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y0 (int_mul (y1 y2) y2)).
Definition term910 (x0 : int) := forall y0 : int, exists y1 : int, (fun y2 : int => fun y3 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt x0 (int_mul y3 y2))) y0 y1.
Definition term908 (x0 : type1550) := forall y0 : int, exists y1 : int, x0 y0 y1.
Definition term907 (x0 : int) := forall y0 : int, exists y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0)).
Definition term723 := forall y0 : int, exists y1 : nat, (fun y2 : int => fun y3 : nat => int_le y2 (int_of_num y3)) y0 y1.
Definition term608 := forall y0 : int, exists y1 : nat, (fun y2 : int => fun y3 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (int_le y2 (int_of_num y3))) y0 y1.
Definition term606 (x0 : type1552) := forall y0 : int, exists y1 : nat, x0 y0 y1.
Definition term603 := forall y0 : int, exists y1 : nat, (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (int_le y0 (int_of_num y1)).
Definition term559 := forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1).
Definition term597 (x0 : int) (x1 : nat) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((fun y0 : nat => int_le x0 (int_of_num y0)) x1).
Definition term973 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> exists y3 : int, int_lt y1 (int_mul y3 y2)) y0).
Definition term967 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt x0 (int_mul y2 y1)) y0).
Definition term638 := exists y0 : int, ~ ((fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) y0).
Definition term1167 (x0 : type1551) (x1 : int) := fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x1 (int_mul (x0 x1 y0) y0)).
Definition term62 (x0 : int) := real_le (real_neg (real_of_int x0)).
Definition term656 (x0 : int -> nat) (x1 : int) := int_le x1 (int_of_num (x0 x1)).
Definition term1011 (x0 : type1551) (x1 : int) (x2 : int) := (~ ((int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2))) -> (int_mul (int_neg (x0 x1 (int_neg x2))) x2) = (int_mul (int_neg (x0 x1 (int_neg x2))) x2).
Definition term633 (x0 : int) := fun y0 : nat => ~ ((fun y1 : nat => int_le x0 (int_of_num y1)) y0).
Definition term652 (x0 : int) (x1 : int) := (~ (int_le x1 x0)) -> int_le x0 x1.
Definition term888 (x0 : int) := fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (exists y1 : int, int_lt x0 (int_mul y1 y0)).
Definition term583 := fun y0 : int => (~ (int_le (int_of_num (NUMERAL 0)) y0)) \/ (exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term631 (x0 : int) (x1 : nat) := ~ ((fun y0 : nat => int_le x0 (int_of_num y0)) x1).
Definition term676 (x0 : int) (x1 : int) := fun y0 : int => int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1).
Definition term327 (x0 : nat) := int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term978 := exists y0 : int, exists y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) /\ (forall y2 : int, ~ (int_lt y0 (int_mul y2 y1))).
Definition term632 (x0 : int) (x1 : nat) := ~ (int_le x0 (int_of_num x1)).
Definition term1068 (x0 : type1551) (x1 : int) (x2 : int) := (~ (int_lt x1 (int_mul (x0 x1 x2) x2))) -> ~ (int_lt (int_of_num (NUMERAL 0)) x2).
Definition term1058 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = x2) /\ ((x1 = x3) /\ (~ (int_lt x2 x3))).
Definition term422 (x0 : int) (x1 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term1130 (x0 : int) := fun y0 : int => exists y1 : int, (fun y2 : int => fun y3 : int => (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y3 y2))) y0 y1.
Definition term918 (x0 : int) := fun y0 : int => exists y1 : int, (fun y2 : int => fun y3 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt x0 (int_mul y3 y2))) y0 y1.
Definition term475 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term1120 (x0 : int) := fun y0 : int => exists y1 : int, (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0)).
Definition term906 (x0 : int) := fun y0 : int => exists y1 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0)).
Definition term1013 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term541 (x0 : nat) := fun y0 : nat => ~ (Peano.le x0 y0).
Definition term582 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term287 (x0 : int) (x1 : int) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term823 (x0 : int) (x1 : int) (x2 : int) := imp ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le x1 x2)).
Definition term904 (x0 : int) (x1 : int) := fun y0 : int => (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ (int_lt x0 (int_mul y0 x1)).
Definition term30 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term407 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term289 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term313 (x0 : int) := forall y0 : int, (int_mul (int_neg x0) y0) = (int_mul x0 (int_neg y0)).
Definition term434 (x0 : int) (x1 : nat) (x2 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_of_int x2)) (real_of_num (NUMERAL 0))).
Definition term499 := forall y0 : nat, (fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) (int_of_num y0).
Definition term3 (x0 : int) := (~ (int_lt (int_of_num (NUMERAL 0)) x0)) /\ (~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term681 (x0 : int) (x1 : int) := (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> False.
Definition term864 := imp (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))).
Definition term572 := imp (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)).
Definition term524 := ((~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term1114 (x0 : int) (x1 : int) := @eq Prop ((x1 = (int_of_num (NUMERAL 0))) \/ (exists y0 : int, int_lt x0 (int_mul y0 x1))).
Definition term1113 (x0 : int) (x1 : int) := @eq Prop ((x1 = (int_of_num (NUMERAL 0))) \/ (exists y0 : int, (fun y1 : int => int_lt x0 (int_mul y1 x1)) y0)).
Definition term528 := ~ (forall y0 : nat, Peano.le y0 y0).
Definition term790 (x0 : int) (x1 : nat) (x2 : int) := (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ ((~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))).
Definition term198 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term653 (x0 : int) := (~ (int_le x0 (int_of_num (NUMERAL 0)))) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term1164 := fun y0 : type1551 => forall y1 : int, forall y2 : int, (y2 = (int_of_num (NUMERAL 0))) \/ (int_lt y1 (int_mul (y0 y1 y2) y2)).
Definition term954 := fun y0 : type1551 => forall y1 : int, forall y2 : int, (~ (int_lt (int_of_num (NUMERAL 0)) y2)) \/ (int_lt y1 (int_mul (y0 y1 y2) y2)).
Definition term125 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0)).
Definition term74 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1092 (x0 : type1551) (x1 : int) (x2 : int) := (int_lt x1 (int_mul (x0 x1 x2) x2)) -> False.
Definition term981 (x0 : int) := or (x0 = (int_of_num (NUMERAL 0))).
Definition term1024 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term997 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x3 = x1) -> (int_lt x0 x1) \/ (~ (int_lt x2 x3)).
Definition term526 := (((~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> ((~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False) -> (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)) -> (forall y0 : nat, Peano.le y0 y0) -> False.
Definition term775 (x0 : int) (x1 : int) := fun y0 : int => ((~ (int_le (int_of_num (NUMERAL 0)) x1)) \/ (~ (int_le x0 y0))) \/ (int_le (int_mul x1 x0) (int_mul x1 y0)).
Definition term517 (x0 : nat) := exists y0 : nat, Peano.le x0 y0.
Definition term153 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term184 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term402 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term299 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))) (real_mul (real_of_int x0) (real_of_int x1)).
Definition term77 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term42 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term203 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term352 (x0 : nat) (x1 : int) := real_add (real_mul (real_of_num x0) (real_of_int x1)).
Definition term1098 := (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term871 := (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term1015 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term290 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term83 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term980 (x0 : int) := or (~ (~ (x0 = (int_of_num (NUMERAL 0))))).
Definition term673 (x0 : int) (x1 : int) (x2 : int) := int_lt x0 (int_mul x1 x2).
Definition term259 (x0 : int) := real_mul (real_of_int x0).
Definition term605 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term275 (x0 : int) (x1 : int) := (real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1))).
Definition term988 (x0 : int) := (fun y0 : int => (y0 = (int_of_num (NUMERAL 0))) \/ ((int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0)))) x0.
Definition term239 (x0 : int) (x1 : int) := (int_le (int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul x0 (int_neg x1))) \/ (int_le (int_add (int_mul x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_neg x0) x1)).
Definition term50 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term518 := fun y0 : nat => exists y1 : nat, Peano.le y0 y1.
Definition term556 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term679 (x0 : int) (x1 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> exists y0 : int, int_lt x0 (int_mul y0 x1).
Definition term44 := real_add (real_of_num (NUMERAL 0)).
Definition term234 (x0 : int) := ~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))))).
Definition term468 (x0 : nat) (x1 : int) (x2 : int) := (~ (~ (((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) /\ (real_le (real_mul (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num x0) (real_of_int x1)))) /\ (real_le (real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))))) -> False.
Definition term310 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_add (real_mul (real_neg (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_mul (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_int x0)) (real_of_int x1)))))) -> False.
Definition term232 (x0 : int) := (~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_le (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))))))) -> False.
Definition term704 (x0 : int) := fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> exists y2 : nat, int_le y1 (int_of_num y2)) -> (forall y1 : int, exists y2 : nat, int_le y1 (int_of_num y2)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : int, int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x0))) -> (forall y1 : int, forall y2 : nat, forall y3 : int, ((int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y2)) /\ (int_le (int_mul (int_of_num y2) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3))) -> int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_le y2 y3)) -> int_le (int_mul y1 y2) (int_mul y1 y3)) -> ~ (forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y1)).
Definition term703 (x0 : int) := fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> exists y2 : nat, int_le y1 (int_of_num y2)) -> (forall y1 : int, exists y2 : nat, int_le y1 (int_of_num y2)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : int, int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x0))) -> (forall y1 : int, forall y2 : nat, forall y3 : int, ((int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y2)) /\ (int_le (int_mul (int_of_num y2) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3))) -> int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_le y2 y3)) -> int_le (int_mul y1 y2) (int_mul y1 y3)) -> (forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y1)) -> False.
Definition term1095 := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term860 := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term685 (x0 : int) (x1 : int) := (((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term354 (x0 : nat) (x1 : int) := real_le (real_of_int (int_add (int_mul (int_of_num x0) x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term255 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_mul (int_neg x0) x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term1001 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((int_lt x0 x1) \/ (~ (int_lt x2 x3)))).
Definition term390 (x0 : int) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term868 := (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term1104 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term1093 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term875 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> ~ (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))).
Definition term858 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term783 (x0 : int) (x1 : nat) (x2 : int) := (fun y0 : int => ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ (~ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0)))) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) y0))) x2.
Definition term544 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term73 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term853 (x0 : int) (x1 : int) := (fun y0 : int => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> exists y2 : nat, int_le y1 (int_of_num y2)) -> (forall y1 : int, exists y2 : nat, int_le y1 (int_of_num y2)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : int, int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x0))) -> (forall y1 : int, forall y2 : nat, forall y3 : int, ((int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y2)) /\ (int_le (int_mul (int_of_num y2) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3))) -> int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y2) y3)) -> (forall y1 : int, forall y2 : int, forall y3 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_le y2 y3)) -> int_le (int_mul y1 y2) (int_mul y1 y3)) -> (forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y1)) -> False) x1.
Definition term587 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term411 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term195 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term455 (x0 : int) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_num x1))) (real_add (real_of_num x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_of_int x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term308 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term24 := int_of_num (NUMERAL (BIT1 0)).
Definition term1006 (x0 : type1551) (x1 : int) (x2 : int) := int_mul (int_neg (x0 x1 (int_neg x2))) x2.
Definition term353 (x0 : nat) (x1 : int) := real_add (real_mul (real_of_num x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term291 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_int x0) (real_of_int x1))).
Definition term199 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term801 (x0 : int) := (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) -> int_le (int_of_num (NUMERAL (BIT1 0))) x0.
Definition term654 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) -> int_le (int_of_num (NUMERAL 0)) x0.
Definition term738 (x0 : int -> nat) := forall y0 : int, int_le y0 (int_of_num (x0 y0)).
Definition term821 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term629 (x0 : int) := ~ (exists y0 : nat, int_le x0 (int_of_num y0)).
Definition term1094 := ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term859 := ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) y1) -> exists y2 : int, int_lt y0 (int_mul y2 y1)) -> (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))) -> (forall y0 : int, (~ (y0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) y0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg y0))) -> (forall y0 : int, forall y1 : int, (int_mul (int_neg y0) y1) = (int_mul y0 (int_neg y1))) -> False.
Definition term684 (x0 : int) (x1 : int) := ((forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False) -> (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> exists y1 : nat, int_le y0 (int_of_num y1)) -> (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1)) -> (~ ((int_le (int_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : int, int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y0 x1))) -> (forall y0 : int, forall y1 : nat, forall y2 : int, ((int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num y1)) /\ (int_le (int_mul (int_of_num y1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2))) -> int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num y1) y2)) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le y1 y2)) -> int_le (int_mul y0 y1) (int_mul y0 y2)) -> (forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) -> False.
Definition term323 (x0 : int) (x1 : nat) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num x1)).
Definition term28 := NUMERAL (BIT1 0).
Definition term6 (x0 : int) := and (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term650 (x0 : int) (x1 : int) := @eq Prop ((int_le x1 x0) \/ (int_le x0 x1)).
Definition term867 := imp (~ (forall y0 : int, forall y1 : int, (~ (y1 = (int_of_num (NUMERAL 0)))) -> exists y2 : int, int_lt y0 (int_mul y2 y1))).
Definition term569 := imp (~ (forall y0 : int, exists y1 : nat, int_le y0 (int_of_num y1))).
Definition term530 := imp (~ (forall y0 : nat, exists y1 : nat, Peano.le y0 y1)).
Definition term267 (x0 : int) (x1 : int) := real_of_int (int_add (int_mul x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term1087 (x0 : int) := imp (~ (~ (int_lt (int_of_num (NUMERAL 0)) x0))).
Definition term661 (x0 : int) := imp (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term649 (x0 : Prop) := x0 -> ~ x0.
Definition term149 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term658 (x0 : int -> nat) (x1 : int) := @eq Prop ((int_le x1 (int_of_num (x0 x1))) \/ (~ (int_le (int_of_num (NUMERAL 0)) x1))).
Definition term318 (x0 : int) (x1 : nat) (x2 : int) := ~ (((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_le (int_mul (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2))) -> int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x1) x2)).
Definition term0 (x0 : int) := ~ (~ ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))).
Definition term1126 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => fun y1 : int => (y0 = (int_of_num (NUMERAL 0))) \/ (int_lt x0 (int_mul y1 y0))) x1 x2.
Definition term914 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => fun y1 : int => (~ (int_lt (int_of_num (NUMERAL 0)) y0)) \/ (int_lt x0 (int_mul y1 y0))) x1 x2.
Definition term146 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term895 (x0 : int) (x1 : int) := exists y0 : int, (~ (int_lt (int_of_num (NUMERAL 0)) x1)) \/ ((fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term86 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term730 := fun y0 : int => exists y1 : nat, (fun y2 : int => fun y3 : nat => int_le y2 (int_of_num y3)) y0 y1.
Definition term616 := fun y0 : int => exists y1 : nat, (fun y2 : int => fun y3 : nat => (~ (int_le (int_of_num (NUMERAL 0)) y2)) \/ (int_le y2 (int_of_num y3))) y0 y1.
Definition term976 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (~ (y2 = (int_of_num (NUMERAL 0)))) -> exists y3 : int, int_lt y1 (int_mul y3 y2)) y0).
Definition term640 := fun y0 : int => ~ ((fun y1 : int => exists y2 : nat, int_le y1 (int_of_num y2)) y0).
Definition term1056 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x0 = x2))) /\ (~ (int_lt x1 x2)).
Definition term257 (x0 : int) (x1 : int) := real_of_int (int_mul x0 (int_neg x1)).
Definition term7 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((int_lt (int_of_num (NUMERAL 0)) x0) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))).
Definition term1039 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (int_lt x0 x1) \/ ((~ (x3 = x1)) \/ (~ (int_lt x2 x3))).
Definition term842 (x0 : nat) (x1 : int) := ~ (~ (int_le (int_mul (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_mul (int_of_num x0) x1))).
Definition term250 (x0 : int) := real_mul (real_neg (real_of_int x0)).
Definition term219 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term171 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term163 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1080 (x0 : int) := ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))) -> int_lt (int_of_num (NUMERAL 0)) x0.
Definition term957 (x0 : int) (x1 : int) := forall y0 : int, ~ ((fun y1 : int => int_lt x0 (int_mul y1 x1)) y0).
Definition term745 (x0 : int) (x1 : int) := forall y0 : int, ~ ((fun y1 : int => int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_mul y1 x1)) y0).
Definition term1078 (x0 : int) := imp (~ ((x0 = (int_of_num (NUMERAL 0))) \/ (int_lt (int_of_num (NUMERAL 0)) (int_neg x0)))).
