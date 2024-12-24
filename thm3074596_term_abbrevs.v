Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) (x1 : nat) := (((~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False.
Definition term109 (x0 : int) (x1 : int) (x2 : int) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term116 := (~ False) -> False.
Definition term138 (x0 : nat) (x1 : int) := int_mul (int_abs (int_of_num x0)) (int_abs (int_of_num (num_of_int (int_abs x1)))).
Definition term87 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => x0 = (Nat.mul x1 y0)) x2).
Definition term51 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (forall y0 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0))).
Definition term102 (x0 : Prop) := ~ (~ x0).
Definition term74 (x0 : nat) (x1 : int) := fun y0 : nat => ~ ((int_of_num y0) = (int_mul (int_of_num x0) x1)).
Definition term59 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0.
Definition term114 (x0 : nat) (x1 : nat) (x2 : int) := ((int_of_num (Nat.mul x1 x0)) = (int_mul (int_of_num x1) x2)) -> False.
Definition term120 (x0 : nat) (x1 : int) := int_of_num (Nat.mul x0 (num_of_int (int_abs x1))).
Definition term101 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term4 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False.
Definition term123 (x0 : int) := (fun y0 : int => forall y1 : int, (int_abs (int_mul y0 y1)) = (int_mul (int_abs y0) (int_abs y1))) x0.
Definition term105 (x0 : int) (x1 : int) := and (x0 = x1).
Definition term45 (x0 : nat) (x1 : nat) (x2 : int) := ~ ((int_of_num x0) = (int_mul (int_of_num x1) x2)).
Definition term147 (x0 : nat) (x1 : nat) := (exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0)) -> exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term107 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term106 (x0 : int) (x1 : int) (x2 : int) := (x1 = x0) /\ (x1 = x2).
Definition term46 (x0 : nat) (x1 : nat) := fun y0 : int => ~ ((fun y1 : int => (int_of_num x0) = (int_mul (int_of_num x1) y1)) y0).
Definition term41 (x0 : nat) (x1 : nat) := ~ (exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0)).
Definition term30 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := and (x0 = (Nat.mul x1 x2)).
Definition term133 (x0 : nat) := @eq int (int_abs (int_of_num x0)).
Definition term57 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y1 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y1))).
Definition term1 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0).
Definition term18 (x0 : nat) := forall y0 : nat, (~ ((exists y1 : nat, y0 = (Nat.mul x0 y1)) -> exists y1 : int, (int_of_num y0) = (int_mul (int_of_num x0) y1))) -> (forall y1 : nat, forall y2 : nat, ((int_of_num y1) = (int_of_num y2)) = (y1 = y2)) -> (forall y1 : nat, forall y2 : nat, (int_mul (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.mul y1 y2))) -> False.
Definition term95 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term112 (x0 : nat) (x1 : nat) := (~ ((int_of_num (Nat.mul x0 x1)) = (int_mul (int_of_num x0) (int_of_num x1)))) -> (int_of_num (Nat.mul x0 x1)) = (int_mul (int_of_num x0) (int_of_num x1)).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))).
Definition term17 (x0 : nat) := fun y0 : nat => (~ ((exists y1 : nat, y0 = (Nat.mul x0 y1)) -> exists y1 : int, (int_of_num y0) = (int_mul (int_of_num x0) y1))) -> (forall y1 : nat, forall y2 : nat, ((int_of_num y1) = (int_of_num y2)) = (y1 = y2)) -> ~ (forall y1 : nat, forall y2 : nat, (int_mul (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.mul y1 y2))).
Definition term33 (x0 : nat) (x1 : int) := int_mul (int_of_num x0) x1.
Definition term50 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (~ (exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))).
Definition term83 (x0 : Prop) := (~ x0) -> x0.
Definition term29 (x0 : nat) := fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term97 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term81 (x0 : nat) (x1 : nat) := (~ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1)))) -> (int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1)).
Definition term99 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term134 (x0 : nat) (x1 : int) := @eq int (int_mul (int_abs (int_of_num x0)) (int_abs x1)).
Definition term122 (x0 : nat) (x1 : int) := int_abs (int_of_num (Nat.mul x0 (num_of_int (int_abs x1)))).
Definition term93 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term3 (x0 : nat) (x1 : nat) := ~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0)).
Definition term61 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0).
Definition term38 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term142 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) (int_abs x0)) -> (int_of_num (num_of_int (int_abs x0))) = (int_abs x0).
Definition term94 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term130 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0))) x1.
Definition term12 := (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False.
Definition term91 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term140 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_of_num (num_of_int x0)) = x0.
Definition term124 (x0 : int) := forall y0 : int, (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0)).
Definition term56 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y0 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0))).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 = (Nat.mul x1 y0)) x2.
Definition term31 := fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term110 (x0 : nat) (x1 : nat) := ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_mul (int_of_num x0) (int_of_num x1))).
Definition term19 (x0 : nat) := forall y0 : nat, (~ ((exists y1 : nat, y0 = (Nat.mul x0 y1)) -> exists y1 : int, (int_of_num y0) = (int_mul (int_of_num x0) y1))) -> (forall y1 : nat, forall y2 : nat, ((int_of_num y1) = (int_of_num y2)) = (y1 = y2)) -> ~ (forall y1 : nat, forall y2 : nat, (int_mul (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.mul y1 y2))).
Definition term40 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term80 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term148 (x0 : nat) (x1 : nat) := ((exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0)) -> exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0)).
Definition term127 (x0 : int) (x1 : int) := int_mul (int_abs x0) (int_abs x1).
Definition term8 := (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False.
Definition term115 (x0 : nat) (x1 : nat) := ((int_of_num (Nat.mul x0 x1)) = (int_mul (int_of_num x0) (int_of_num x1))) -> False.
Definition term43 (x0 : nat) (x1 : nat) (x2 : int) := (fun y0 : int => (int_of_num x0) = (int_mul (int_of_num x1) y0)) x2.
Definition term37 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term75 (x0 : nat) (x1 : int) (x2 : nat) := (fun y0 : nat => ~ ((int_of_num y0) = (int_mul (int_of_num x0) x1))) x2.
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.mul x1 y0).
Definition term139 (x0 : int) := int_of_num (num_of_int (int_abs x0)).
Definition term14 (x0 : nat) (x1 : nat) := imp (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.mul x2 x0)) /\ (forall y0 : int, ~ ((int_of_num x1) = (int_mul (int_of_num x2) y0))).
Definition term15 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> ~ (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))).
Definition term98 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term25 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term32 := forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term23 := forall y0 : nat, forall y1 : nat, (~ ((exists y2 : nat, y1 = (Nat.mul y0 y2)) -> exists y2 : int, (int_of_num y1) = (int_mul (int_of_num y0) y2))) -> (forall y2 : nat, forall y3 : nat, ((int_of_num y2) = (int_of_num y3)) = (y2 = y3)) -> ~ (forall y2 : nat, forall y3 : nat, (int_mul (int_of_num y2) (int_of_num y3)) = (int_of_num (Nat.mul y2 y3))).
Definition term22 := forall y0 : nat, forall y1 : nat, (~ ((exists y2 : nat, y1 = (Nat.mul y0 y2)) -> exists y2 : int, (int_of_num y1) = (int_mul (int_of_num y0) y2))) -> (forall y2 : nat, forall y3 : nat, ((int_of_num y2) = (int_of_num y3)) = (y2 = y3)) -> (forall y2 : nat, forall y3 : nat, (int_mul (int_of_num y2) (int_of_num y3)) = (int_of_num (Nat.mul y2 y3))) -> False.
Definition term10 := forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1)).
Definition term126 (x0 : int) (x1 : int) := int_abs (int_mul x0 x1).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term39 (x0 : int -> Prop) := ~ (ex x0).
Definition term144 (x0 : int) := int_abs (int_of_num (num_of_int (int_abs x0))).
Definition term5 (x0 : nat) (x1 : nat) := ((~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False.
Definition term129 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0)).
Definition term92 (x0 : int) (x1 : int) (x2 : int) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term96 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term121 (x0 : nat) := int_abs (int_of_num x0).
Definition term55 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term137 (x0 : nat) (x1 : int) := int_abs (int_mul (int_of_num x0) (int_of_num (num_of_int (int_abs x1)))).
Definition term27 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term82 (x0 : nat) (x1 : nat) := ~ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))).
Definition term90 (x0 : int) (x1 : int) (x2 : int) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term60 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0.
Definition term7 (x0 : nat) (x1 : nat) := (((~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False) -> ((~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False) -> (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) -> False.
Definition term44 (x0 : nat) (x1 : nat) (x2 : int) := ~ ((fun y0 : int => (int_of_num x0) = (int_mul (int_of_num x1) y0)) x2).
Definition term104 (x0 : int) (x1 : int) := and (~ (~ (x0 = x1))).
Definition term78 (x0 : nat) (x1 : int) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ ((int_of_num y0) = (int_mul (int_of_num x0) x1))) x2).
Definition term119 (x0 : nat) (x1 : int) := Nat.mul x0 (num_of_int (int_abs x1)).
Definition term88 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term84 (x0 : nat) (x1 : nat) := (~ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_mul (int_of_num x0) (int_of_num x1)))) -> (int_mul (int_of_num x0) (int_of_num x1)) = (int_mul (int_of_num x0) (int_of_num x1)).
Definition term118 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ ((exists y1 : nat, y0 = (Nat.mul x0 y1)) -> exists y1 : int, (int_of_num y0) = (int_mul (int_of_num x0) y1))) -> (forall y1 : nat, forall y2 : nat, ((int_of_num y1) = (int_of_num y2)) = (y1 = y2)) -> (forall y1 : nat, forall y2 : nat, (int_mul (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.mul y1 y2))) -> False) x1.
Definition term16 (x0 : nat) := fun y0 : nat => (~ ((exists y1 : nat, y0 = (Nat.mul x0 y1)) -> exists y1 : int, (int_of_num y0) = (int_mul (int_of_num x0) y1))) -> (forall y1 : nat, forall y2 : nat, ((int_of_num y1) = (int_of_num y2)) = (y1 = y2)) -> (forall y1 : nat, forall y2 : nat, (int_mul (int_of_num y1) (int_of_num y2)) = (int_of_num (Nat.mul y1 y2))) -> False.
Definition term54 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term68 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y1 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y1))).
Definition term128 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1))) x0.
Definition term117 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, y1 = (Nat.mul y0 y2)) -> exists y2 : int, (int_of_num y1) = (int_mul (int_of_num y0) y2))) -> (forall y2 : nat, forall y3 : nat, ((int_of_num y2) = (int_of_num y3)) = (y2 = y3)) -> (forall y2 : nat, forall y3 : nat, (int_mul (int_of_num y2) (int_of_num y3)) = (int_of_num (Nat.mul y2 y3))) -> False) x0.
Definition term71 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term143 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term49 (x0 : nat) (x1 : nat) := and (exists y0 : nat, x0 = (Nat.mul x1 y0)).
Definition term125 (x0 : int) (x1 : int) := (fun y0 : int => (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0))) x1.
Definition term146 (x0 : nat) := int_mul (int_abs (int_of_num x0)).
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : int) := (fun y0 : int => ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0))) x2.
Definition term85 (x0 : nat) (x1 : nat) := ~ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_mul (int_of_num x0) (int_of_num x1))).
Definition term100 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => x1 = (Nat.mul x2 y0)) x0) /\ (forall y0 : int, ~ ((int_of_num x1) = (int_mul (int_of_num x2) y0))).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : int => ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0)).
Definition term13 := (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) -> ~ (forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))).
Definition term26 (x0 : nat) := fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term135 (x0 : nat) (x1 : int) := int_mul (int_of_num x0) (int_of_num (num_of_int (int_abs x1))).
Definition term76 (x0 : int) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((int_of_num y0) = (int_mul (int_of_num x1) x0))) (Nat.mul x1 x2).
Definition term79 (x0 : nat) (x1 : nat) (x2 : int) := @eq Prop (~ ((int_of_num x0) = (int_mul (int_of_num x1) x2))).
Definition term35 (x0 : nat) (x1 : nat) := exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0).
Definition term136 (x0 : int) := num_of_int (int_abs x0).
Definition term132 (x0 : nat) (x1 : int) := int_mul (int_abs (int_of_num x0)) (int_abs x1).
Definition term111 (x0 : nat) (x1 : nat) := (((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.mul x0 x1))) /\ ((int_mul (int_of_num x0) (int_of_num x1)) = (int_mul (int_of_num x0) (int_of_num x1)))) -> (int_of_num (Nat.mul x0 x1)) = (int_mul (int_of_num x0) (int_of_num x1)).
Definition term28 := fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1)).
Definition term108 (x0 : int) (x1 : int) (x2 : int) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term70 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.mul x1 y0)) /\ (forall y1 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y1))).
Definition term63 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, x0 = (Nat.mul x1 y0)) /\ (forall y0 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0)))).
Definition term62 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => x0 = (Nat.mul x1 y1)) y0) /\ (forall y0 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y0)))).
Definition term86 (x0 : int) (x1 : int) (x2 : int) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term141 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term2 (x0 : nat) (x1 : nat) := (~ ((exists y0 : nat, x0 = (Nat.mul x1 y0)) -> exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0))) -> False.
Definition term145 (x0 : int) := int_abs (int_abs x0).
Definition term103 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term89 (x0 : int) (x1 : int) := or (~ (x0 = x1)).
Definition term11 := imp (forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)).
Definition term69 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.mul x1 y0)) /\ (forall y1 : int, ~ ((int_of_num x0) = (int_mul (int_of_num x1) y1))).
Definition term131 (x0 : nat) (x1 : int) := int_abs (int_mul (int_of_num x0) x1).
Definition term113 (x0 : nat) (x1 : nat) := ~ ((int_of_num (Nat.mul x0 x1)) = (int_mul (int_of_num x0) (int_of_num x1))).
Definition term24 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term77 (x0 : nat) (x1 : nat) (x2 : int) := ~ ((int_of_num (Nat.mul x1 x0)) = (int_mul (int_of_num x1) x2)).
Definition term21 := fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, y1 = (Nat.mul y0 y2)) -> exists y2 : int, (int_of_num y1) = (int_mul (int_of_num y0) y2))) -> (forall y2 : nat, forall y3 : nat, ((int_of_num y2) = (int_of_num y3)) = (y2 = y3)) -> ~ (forall y2 : nat, forall y3 : nat, (int_mul (int_of_num y2) (int_of_num y3)) = (int_of_num (Nat.mul y2 y3))).
Definition term20 := fun y0 : nat => forall y1 : nat, (~ ((exists y2 : nat, y1 = (Nat.mul y0 y2)) -> exists y2 : int, (int_of_num y1) = (int_mul (int_of_num y0) y2))) -> (forall y2 : nat, forall y3 : nat, ((int_of_num y2) = (int_of_num y3)) = (y2 = y3)) -> (forall y2 : nat, forall y3 : nat, (int_mul (int_of_num y2) (int_of_num y3)) = (int_of_num (Nat.mul y2 y3))) -> False.
Definition term34 (x0 : nat) (x1 : nat) := fun y0 : int => (int_of_num x0) = (int_mul (int_of_num x1) y0).
Definition term42 (x0 : nat) (x1 : nat) := forall y0 : int, ~ ((fun y1 : int => (int_of_num x0) = (int_mul (int_of_num x1) y1)) y0).
