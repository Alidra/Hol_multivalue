Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term422 (x0 : int) (x1 : int) (x2 : int) := or ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term240 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term59 (x0 : nat) := (fun y0 : nat => y0 = y0) x0.
Definition term371 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term87 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0) /\ (x0 = x0).
Definition term145 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x0 y0)) /\ (forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)).
Definition term431 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term34 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add x0 (Nat.add x1 y0)).
Definition term143 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0) /\ ((fun y1 : nat => forall y2 : nat, ((Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) /\ (x0 = x0)) y0).
Definition term125 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) /\ (y1 = y1)) y0).
Definition term301 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term313 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term348 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add x0 (Nat.add x1 y0))) x2).
Definition term1 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 (x0 y0 y1) y2)) /\ (forall y0 : a0, (x0 (@neutral a0 x0) y0) = y0)).
Definition term27 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term355 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term326 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term396 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term138 (x0 : nat) := @eq Prop ((forall y0 : nat, (Nat.add x0 y0) = (Nat.add x0 y0)) /\ (forall y0 : nat, forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0))).
Definition term137 (x0 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) /\ (x0 = x0)) y0)).
Definition term120 := @eq Prop ((forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0))).
Definition term119 := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) /\ (y1 = y1)) y0)).
Definition term63 := @eq Prop ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (forall y0 : nat, y0 = y0)).
Definition term62 := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0) /\ (forall y0 : nat, (fun y1 : nat => y1 = y1) y0)).
Definition term362 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.add x0 (Nat.add x1 y1)) = (Nat.add x0 (Nat.add x1 y1))) y0.
Definition term129 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0) /\ ((fun y1 : nat => forall y2 : nat, ((Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) /\ (x0 = x0)) y0).
Definition term111 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0) /\ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) /\ (y1 = y1)) y0).
Definition term54 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0) /\ ((fun y1 : nat => y1 = y1) y0).
Definition term363 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term142 (x0 : nat) (x1 : nat) := ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ (forall y0 : nat, ((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1)).
Definition term300 (x0 : nat) := real_neg (real_of_num x0).
Definition term387 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0))))))).
Definition term216 := real_of_int (int_of_num (NUMERAL 0)).
Definition term288 (x0 : Prop) := ~ (~ x0).
Definition term217 := real_of_num (NUMERAL 0).
Definition term116 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)) x0.
Definition term55 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term267 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term264 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2)))) \/ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2)))).
Definition term376 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term324 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term172 (x0 : nat) (x1 : nat) (x2 : nat) := int_add (int_of_num x0) (int_of_num (Nat.add x1 x2)).
Definition term206 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2))).
Definition term42 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term195 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_add x2 x0) = (int_add x2 x0))) \/ ((~ ((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1)))) \/ (~ (x2 = x2))).
Definition term249 (x0 : int) (x1 : int) (x2 : int) := int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0))).
Definition term150 (x0 : nat) (x1 : nat) := ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ (forall y0 : nat, (fun y1 : nat => ((Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) /\ (x1 = x1)) y0).
Definition term250 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term243 (x0 : int) (x1 : int) := or (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))).
Definition term292 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ ((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))).
Definition term214 := int_of_num (NUMERAL 0).
Definition term222 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term437 (x0 : int) (x1 : int) (x2 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))))).
Definition term176 (x0 : nat) (x1 : nat) (x2 : nat) := @eq int (int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num x2))).
Definition term361 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term365 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term394 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) := ((int_add (int_of_num x2) (int_of_num x0)) = (int_add (int_of_num x2) (int_of_num x0))) /\ (((int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1))) = (int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1)))) /\ ((int_of_num x2) = (int_of_num x2))).
Definition term238 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term347 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term427 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term188 (x0 : int) (x1 : int) (x2 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x2) -> (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)))).
Definition term413 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term308 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add x0 (Nat.add x1 y0)).
Definition term335 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term223 (x0 : int) (x1 : int) := ~ ((int_add x0 x1) = (int_add x0 x1)).
Definition term128 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) /\ (x0 = x0)) y0).
Definition term110 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) /\ (y1 = y1)) y0).
Definition term53 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0) /\ (forall y0 : nat, (fun y1 : nat => y1 = y1) y0).
Definition term109 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)).
Definition term161 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ (((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1)).
Definition term350 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term270 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term278 (x0 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term423 (x0 : int) (x1 : int) (x2 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) \/ (((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))).
Definition term416 (x0 : int) (x1 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term322 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term126 := fun y0 : nat => (forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ (forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)).
Definition term260 (x0 : int) (x1 : int) (x2 : int) := real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term154 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => ((Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) /\ (x1 = x1)) y0.
Definition term132 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0.
Definition term94 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.add x0 (Nat.add x1 y1)) = (Nat.add x0 (Nat.add x1 y1))) y0.
Definition term375 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term4 := Nat.add (@neutral nat Nat.add).
Definition term432 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term359 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term354 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term332 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 (x0 : nat) (x1 : nat) := fun y0 : nat => ((int_add (int_of_num x1) (int_of_num x0)) = (int_add (int_of_num x1) (int_of_num x0))) /\ (((int_add (int_of_num x1) (int_add (int_of_num x0) (int_of_num y0))) = (int_add (int_of_num x1) (int_add (int_of_num x0) (int_of_num y0)))) /\ ((int_of_num x1) = (int_of_num x1))).
Definition term299 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term52 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term418 (x0 : int) (x1 : int) (x2 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))).
Definition term411 (x0 : int) (x1 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) /\ x1.
Definition term220 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x2 x0) = (Nat.add x2 x0)) /\ (((Nat.add x2 (Nat.add x0 x1)) = (Nat.add x2 (Nat.add x0 x1))) /\ (x2 = x2)).
Definition term390 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term261 (x0 : int) (x1 : int) (x2 : int) := real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))).
Definition term321 (x0 : int) := real_ge (real_of_int x0).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term0 (a0 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) = ((forall y1 : a0, forall y2 : a0, (y0 y1 y2) = (y0 y2 y1)) /\ ((forall y1 : a0, forall y2 : a0, forall y3 : a0, (y0 y1 (y0 y2 y3)) = (y0 (y0 y1 y2) y3)) /\ (forall y1 : a0, (y0 (@neutral a0 y0) y1) = y1)))) x0.
Definition term392 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_add (real_add (real_of_int x1) (real_of_int x2)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term391 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term97 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1)).
Definition term96 (x0 : nat) (x1 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => (Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) y0) /\ (x1 = x1)).
Definition term259 (x0 : int) (x1 : int) (x2 : int) := real_le (real_of_int (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term439 (x0 : nat) (x1 : nat) (x2 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x2)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_add (int_of_num x2) (int_of_num x0)) = (int_add (int_of_num x2) (int_of_num x0))) /\ (((int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1))) = (int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1)))) /\ ((int_of_num x2) = (int_of_num x2))).
Definition term88 (x0 : nat) := fun y0 : nat => (forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) := and ((int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num x2))) = (int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num x2)))).
Definition term339 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term303 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term21 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term253 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int x0) (real_of_int (int_add x1 x2)).
Definition term255 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2)).
Definition term414 (x0 : int) (x1 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term82 (x0 : nat) := @eq Prop ((forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)).
Definition term81 (x0 : nat) := @eq Prop ((forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0) /\ (x0 = x0)).
Definition term415 (x0 : int) (x1 : int) := or ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term230 (x0 : int) (x1 : int) := real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term425 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term344 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term242 (x0 : int) (x1 : int) := or (int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1)).
Definition term342 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term74 (x0 : nat -> Prop) (x1 : Prop) := forall y0 : nat, (x0 y0) /\ x1.
Definition term279 (x0 : int) (x1 : int) (x2 : int) := or (~ ((int_add x0 (int_add x1 x2)) = (int_add x0 (int_add x1 x2)))).
Definition term320 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term357 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term419 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term330 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term271 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term315 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term426 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term401 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term22 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term417 (x0 : int) (x1 : int) (x2 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))).
Definition term410 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term275 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term194 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_add x2 x0) = (int_add x2 x0))) \/ (~ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term144 (x0 : nat) := fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x0 y0)) /\ (forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)).
Definition term307 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term430 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term395 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term424 (x0 : int) (x1 : int) (x2 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term360 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term346 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_add (real_of_int x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term353 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ ((fun y0 : nat => ((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1)) x2).
Definition term209 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) /\ ((int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ ((~ ((int_add x2 x0) = (int_add x2 x0))) \/ ((~ ((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1)))) \/ (~ (x2 = x2)))))).
Definition term319 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)) x1.
Definition term77 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term241 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)).
Definition term219 := real_le (real_of_num (NUMERAL 0)).
Definition term228 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term433 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term105 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0).
Definition term45 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1).
Definition term29 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term23 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term43 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add x0 y0).
Definition term328 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term329 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term9 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term8 (x0 : nat) := @eq nat (Nat.add (@neutral nat Nat.add) x0).
Definition term234 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)).
Definition term254 (x0 : int) := real_add (real_of_int x0).
Definition term186 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term89 (x0 : nat) := forall y0 : nat, (forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0).
Definition term289 (x0 : int) (x1 : int) (x2 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))))))).
Definition term435 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term48 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (forall y0 : nat, y0 = y0)).
Definition term18 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) /\ (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0)).
Definition term3 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) /\ (forall y0 : nat, (Nat.add (@neutral nat Nat.add) y0) = y0)).
Definition term2 (x0 : type1606) := (forall y0 : nat, forall y1 : nat, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : nat, forall y1 : nat, forall y2 : nat, (x0 y0 (x0 y1 y2)) = (x0 (x0 y0 y1) y2)) /\ (forall y0 : nat, (x0 (@neutral nat x0) y0) = y0)).
Definition term200 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ ((~ ((int_add x2 x0) = (int_add x2 x0))) \/ ((~ ((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1)))) \/ (~ (x2 = x2)))).
Definition term349 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term409 (x0 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term215 (x0 : nat) := real_of_int (int_of_num x0).
Definition term60 := fun y0 : nat => (fun y1 : nat => y1 = y1) y0.
Definition term245 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_add x0 (int_add x1 x2)) = (int_add x0 (int_add x1 x2))).
Definition term406 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term368 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term412 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term364 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term314 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term265 (x0 : int) := ~ (x0 = x0).
Definition term190 (x0 : int) (x1 : int) (x2 : int) := ~ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)).
Definition term229 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term85 (x0 : nat) (x1 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.add x1 (Nat.add y0 y1)) = (Nat.add x1 (Nat.add y0 y1))) x0) /\ (x1 = x1).
Definition term351 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term122 (x0 : nat) := and (forall y0 : nat, (Nat.add x0 y0) = (Nat.add x0 y0)).
Definition term84 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add x0 (Nat.add x1 y0))).
Definition term306 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term44 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add x0 y0).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term345 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add x0 (Nat.add x1 x2)).
Definition term41 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (forall y0 : nat, y0 = y0).
Definition term16 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) /\ (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term15 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) /\ (forall y0 : nat, (Nat.add (@neutral nat Nat.add) y0) = y0).
Definition term434 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term340 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term189 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)).
Definition term168 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.add x0 x1)).
Definition term252 (x0 : int) (x1 : int) (x2 : int) := real_of_int (int_add x0 (int_add x1 x2)).
Definition term7 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term356 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term327 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) := ((int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1))) = (int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1)))) /\ ((int_of_num x2) = (int_of_num x2)).
Definition term76 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0) /\ (x0 = x0).
Definition term285 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))).
Definition term185 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((int_add (int_of_num y0) (int_of_num y1)) = (int_add (int_of_num y0) (int_of_num y1))) /\ (((int_add (int_of_num y0) (int_add (int_of_num y1) (int_of_num y2))) = (int_add (int_of_num y0) (int_add (int_of_num y1) (int_of_num y2)))) /\ ((int_of_num y0) = (int_of_num y0))).
Definition term183 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((int_add (int_of_num x0) (int_of_num y0)) = (int_add (int_of_num x0) (int_of_num y0))) /\ (((int_add (int_of_num x0) (int_add (int_of_num y0) (int_of_num y1))) = (int_add (int_of_num x0) (int_add (int_of_num y0) (int_of_num y1)))) /\ ((int_of_num x0) = (int_of_num x0))).
Definition term165 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y1)) /\ (((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)).
Definition term163 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y0)) /\ (((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)).
Definition term108 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0).
Definition term106 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0).
Definition term46 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1).
Definition term39 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2)).
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1)).
Definition term30 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term26 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term373 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term274 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term149 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 /\ (x1 y0).
Definition term123 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) x0) /\ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)) x0).
Definition term337 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term61 := forall y0 : nat, (fun y1 : nat => y1 = y1) y0.
Definition term388 (x0 : int) (x1 : int) (x2 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term381 (x0 : int) (x1 : int) (x2 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term323 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term244 (x0 : int) (x1 : int) := (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))).
Definition term277 (x0 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term341 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term13 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term12 := forall y0 : nat, (Nat.add (@neutral nat Nat.add) y0) = y0.
Definition term224 (x0 : int) (x1 : int) := (int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1)) \/ (int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1)).
Definition term227 (x0 : int) (x1 : int) := int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term311 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term379 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term231 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term397 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term156 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.add x1 x0) = (Nat.add x1 x0)) /\ (forall y0 : nat, ((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1))).
Definition term155 (x0 : nat) (x1 : nat) := @eq Prop (((Nat.add x1 x0) = (Nat.add x1 x0)) /\ (forall y0 : nat, (fun y1 : nat => ((Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) /\ (x1 = x1)) y0)).
Definition term389 (x0 : int) (x1 : int) (x2 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term429 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term269 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term358 := S (Nat.add 0 0).
Definition term393 (x0 : int) (x1 : int) (x2 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term304 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term291 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ ((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))).
Definition term173 (x0 : nat) := int_add (int_of_num x0).
Definition term203 (x0 : int) (x1 : int) (x2 : int) := ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)).
Definition term402 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term302 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term421 (x0 : int) (x1 : int) (x2 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term334 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term31 := fun y0 : nat => y0 = y0.
Definition term399 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term290 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)).
Definition term147 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 /\ (x1 y0).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term51 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term266 (x0 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term148 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (forall y0 : nat, x1 y0).
Definition term378 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term256 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_add x0 (int_add x1 x2))).
Definition term6 (x0 : nat) := Nat.add (@neutral nat Nat.add) x0.
Definition term247 (x0 : int) (x1 : int) (x2 : int) := int_le (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_add x1 x2)).
Definition term294 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ ((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))).
Definition term287 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))))).
Definition term366 := real_mul (real_of_num (NUMERAL 0)).
Definition term196 (x0 : int) (x1 : int) (x2 : int) := ~ (((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2))).
Definition term251 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int (int_add x0 (int_add x1 x2))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term208 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)))).
Definition term124 (x0 : nat) := (forall y0 : nat, (Nat.add x0 y0) = (Nat.add x0 y0)) /\ (forall y0 : nat, forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)).
Definition term211 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)).
Definition term83 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) x1).
Definition term140 (x0 : nat) (x1 : nat) := and ((Nat.add x0 x1) = (Nat.add x0 x1)).
Definition term273 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term440 (x0 : nat) (x1 : nat) (x2 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_add (int_of_num x2) (int_of_num x0)) = (int_add (int_of_num x2) (int_of_num x0))) /\ (((int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1))) = (int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1)))) /\ ((int_of_num x2) = (int_of_num x2))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term187 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term309 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := int_of_num (Nat.add x0 (Nat.add x1 x2)).
Definition term400 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term385 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term370 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term210 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x2) -> (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2))).
Definition term221 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) := int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num x2)).
Definition term333 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term283 (x0 : int) (x1 : int) (x2 : int) := ((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))).
Definition term5 := Nat.add (NUMERAL 0).
Definition term65 (x0 : nat) := and (forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))).
Definition term47 := and (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)).
Definition term40 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))).
Definition term17 := and (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term14 := and (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)).
Definition term198 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Nat.add x2 (Nat.add x0 y0)) = (Nat.add x2 (Nat.add x0 y0))) x1) /\ (x2 = x2).
Definition term66 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) x0) /\ ((fun y0 : nat => y0 = y0) x0).
Definition term276 (x0 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term32 := forall y0 : nat, y0 = y0.
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1)) x2.
Definition term338 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term135 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) /\ (x0 = x0)) y0.
Definition term117 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) /\ (y1 = y1)) y0.
Definition term113 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0.
Definition term78 (x0 : nat) := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0.
Definition term56 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0.
Definition term73 (x0 : nat -> Prop) (x1 : Prop) := (forall y0 : nat, x0 y0) /\ x1.
Definition term296 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term212 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term112 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) x0.
Definition term441 (x0 : nat) (x1 : nat) (x2 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_add (int_of_num x2) (int_of_num x0)) = (int_add (int_of_num x2) (int_of_num x0))) /\ (((int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1))) = (int_add (int_of_num x2) (int_add (int_of_num x0) (int_of_num x1)))) /\ ((int_of_num x2) = (int_of_num x2))).
Definition term383 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0))))).
Definition term293 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ ((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))).
Definition term286 (x0 : int) (x1 : int) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))).
Definition term70 := forall y0 : nat, (forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0).
Definition term204 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)))).
Definition term282 (x0 : int) (x1 : int) := or ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))).
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) := @eq int (int_of_num (Nat.add x0 (Nat.add x1 x2))).
Definition term169 (x0 : nat) (x1 : nat) := @eq int (int_add (int_of_num x0) (int_of_num x1)).
Definition term316 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term91 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) y0) /\ (x1 = x1).
Definition term408 (x0 : int) := or ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term297 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term102 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) y0) /\ (x1 = x1).
Definition term405 (x0 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term160 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ (((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1)).
Definition term193 (x0 : int) (x1 : int) := or (~ ((int_add x0 x1) = (int_add x0 x1))).
Definition term312 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term205 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ ((~ ((int_add x2 x0) = (int_add x2 x0))) \/ ((~ ((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1)))) \/ (~ (x2 = x2))))).
Definition term318 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term369 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term236 := real_of_num (NUMERAL (BIT1 0)).
Definition term438 (x0 : int) (x1 : int) (x2 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))))).
Definition term213 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term403 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term280 (x0 : int) (x1 : int) (x2 : int) := or ((real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2)))) \/ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))))).
Definition term377 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term263 (x0 : int) (x1 : int) (x2 : int) := or (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2)))).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) /\ x1.
Definition term159 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ ((fun y1 : nat => ((Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) /\ (x1 = x1)) y0).
Definition term284 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term75 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0) /\ (x0 = x0).
Definition term67 (x0 : nat) := (forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0).
Definition term133 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0).
Definition term115 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0).
Definition term95 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (fun y1 : nat => (Nat.add x0 (Nat.add x1 y1)) = (Nat.add x0 (Nat.add x1 y1))) y0).
Definition term80 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0).
Definition term58 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0).
Definition term121 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) x0).
Definition term64 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) x0).
Definition term197 (x0 : int) (x1 : int) (x2 : int) := ((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2).
Definition term130 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add x0 y0)) x1.
Definition term281 (x0 : int) (x1 : int) (x2 : int) := ((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))).
Definition term343 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term428 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term384 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))).
Definition term104 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1).
Definition term69 := fun y0 : nat => (forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0).
Definition term131 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.add x0 y1) = (Nat.add x0 y1)) y0.
Definition term420 (x0 : int) (x1 : int) (x2 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term235 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term310 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term386 (x0 : int) (x1 : int) (x2 : int) := real_sub (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term127 := forall y0 : nat, (forall y1 : nat, (Nat.add y0 y1) = (Nat.add y0 y1)) /\ (forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)).
Definition term11 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term10 := fun y0 : nat => (Nat.add (@neutral nat Nat.add) y0) = y0.
Definition term246 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_add x1 x2))) \/ (int_le (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_add x1 x2))).
Definition term262 (x0 : int) (x1 : int) (x2 : int) := or (int_le (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_add x1 x2))).
Definition term139 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Nat.add x0 y0) = (Nat.add x0 y0)) x1).
Definition term199 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)))).
Definition term207 (x0 : int) (x1 : int) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2)).
Definition term192 (x0 : int) (x1 : int) (x2 : int) := int_add x0 (int_add x1 x2).
Definition term170 (x0 : nat) (x1 : nat) := and ((int_add (int_of_num x0) (int_of_num x1)) = (int_add (int_of_num x0) (int_of_num x1))).
Definition term103 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1).
Definition term202 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term382 (x0 : int) (x1 : int) (x2 : int) := real_add (real_of_int x0) (real_add (real_add (real_of_int x1) (real_of_int x2)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term272 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term166 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term258 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))) (real_of_num (NUMERAL (BIT1 0))).
Definition term372 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term404 (x0 : int) (x1 : int) (x2 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x2) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))).
Definition term191 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1)))) \/ (~ (x2 = x2)).
Definition term331 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term226 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x0 x1)).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x2 (Nat.add x0 x1)) = (Nat.add x2 (Nat.add x0 x1))) /\ (x2 = x2).
Definition term325 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_int x1)).
Definition term352 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term298 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term218 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term380 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term305 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term233 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)).
Definition term136 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) /\ (x0 = x0)) y0.
Definition term118 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, ((Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) /\ (y1 = y1)) y0.
Definition term114 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add y1 y2) = (Nat.add y1 y2)) y0.
Definition term79 (x0 : nat) := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Nat.add x0 (Nat.add y1 y2)) = (Nat.add x0 (Nat.add y1 y2))) y0.
Definition term57 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0.
Definition term317 := real_div (real_of_num (NUMERAL 0)).
Definition term374 := real_add (real_of_num (NUMERAL 0)).
Definition term248 (x0 : int) (x1 : int) (x2 : int) := real_le (real_of_int (int_add (int_add x0 (int_add x1 x2)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x0 (int_add x1 x2))).
Definition term436 (x0 : int) (x1 : int) (x2 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0))) \/ (real_le (real_add (real_add (real_of_int x2) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_of_int x0)))) \/ (((real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x2) (real_add (real_of_int x0) (real_of_int x1))))) \/ ((real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)) \/ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))))))) -> False.
Definition term151 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x1 x0) = (Nat.add x1 x0)) /\ ((fun y1 : nat => ((Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) /\ (x1 = x1)) y0).
Definition term239 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term367 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term398 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term232 := int_of_num (NUMERAL (BIT1 0)).
Definition term268 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term167 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term182 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((int_add (int_of_num x0) (int_of_num y0)) = (int_add (int_of_num x0) (int_of_num y0))) /\ (((int_add (int_of_num x0) (int_add (int_of_num y0) (int_of_num y1))) = (int_add (int_of_num x0) (int_add (int_of_num y0) (int_of_num y1)))) /\ ((int_of_num x0) = (int_of_num x0))).
Definition term162 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y0)) /\ (((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)).
Definition term36 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1)).
Definition term237 := NUMERAL (BIT1 0).
Definition term257 (x0 : int) (x1 : int) (x2 : int) := real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_int x2))).
Definition term90 (x0 : nat) (x1 : nat) := (forall y0 : nat, (fun y1 : nat => (Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) y0) /\ (x1 = x1).
Definition term86 (x0 : nat) (x1 : nat) := (forall y0 : nat, (Nat.add x1 (Nat.add x0 y0)) = (Nat.add x1 (Nat.add x0 y0))) /\ (x1 = x1).
Definition term181 (x0 : nat) (x1 : nat) := forall y0 : nat, ((int_add (int_of_num x1) (int_of_num x0)) = (int_add (int_of_num x1) (int_of_num x0))) /\ (((int_add (int_of_num x1) (int_add (int_of_num x0) (int_of_num y0))) = (int_add (int_of_num x1) (int_add (int_of_num x0) (int_of_num y0)))) /\ ((int_of_num x1) = (int_of_num x1))).
Definition term184 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((int_add (int_of_num y0) (int_of_num y1)) = (int_add (int_of_num y0) (int_of_num y1))) /\ (((int_add (int_of_num y0) (int_add (int_of_num y1) (int_of_num y2))) = (int_add (int_of_num y0) (int_add (int_of_num y1) (int_of_num y2)))) /\ ((int_of_num y0) = (int_of_num y0))).
Definition term164 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y1)) /\ (((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0)).
Definition term107 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2))) /\ (y0 = y0).
Definition term38 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add y0 (Nat.add y1 y2)).
Definition term25 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term336 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term68 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add y1 (Nat.add y2 y3))) y0) /\ ((fun y1 : nat => y1 = y1) y0).
Definition term141 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.add x0 y0) = (Nat.add x0 y0)) x1) /\ ((fun y0 : nat => forall y1 : nat, ((Nat.add x0 (Nat.add y0 y1)) = (Nat.add x0 (Nat.add y0 y1))) /\ (x0 = x0)) x1).
Definition term407 (x0 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term146 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (forall y0 : a0, x1 y0).
Definition term201 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ((int_add x2 x0) = (int_add x2 x0)) /\ (((int_add x2 (int_add x0 x1)) = (int_add x2 (int_add x0 x1))) /\ (x2 = x2))).
Definition term295 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term153 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Nat.add x1 (Nat.add x0 y1)) = (Nat.add x1 (Nat.add x0 y1))) /\ (x1 = x1)) y0.
Definition term225 (x0 : int) (x1 : int) := int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1).
