Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term47 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1)).
Definition term52 := fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1)).
Definition term46 := fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1)).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term45 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term65 (x0 : nat) := fun y0 : int => (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0)).
Definition term37 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term87 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term53 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1))) x0.
Definition term78 (x0 : nat) := fun y0 : nat => (fun y1 : int => (num_of_int (int_mul (int_of_num x0) y1)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y1))) (int_of_num y0).
Definition term80 (x0 : nat) := forall y0 : nat, (num_of_int (int_mul (int_of_num x0) (int_of_num y0))) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int (int_of_num y0))).
Definition term16 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term58 (x0 : nat) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1))) (int_of_num x0).
Definition term82 (x0 : nat) (x1 : nat) := @eq nat (num_of_int (int_mul (int_of_num x0) (int_of_num x1))).
Definition term59 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0)).
Definition term44 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term29 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term25 (x0 : int) (x1 : int) := Nat.mul (num_of_int x0) (num_of_int x1).
Definition term68 (x0 : nat) (x1 : int) := Nat.mul (num_of_int (int_of_num x0)) (num_of_int x1).
Definition term33 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul x0 y1)) = (Nat.mul (num_of_int x0) (num_of_int y1))) y0.
Definition term17 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term26 (x0 : int) := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term14 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term67 (x0 : nat) (x1 : int) := num_of_int (int_mul (int_of_num x0) x1).
Definition term15 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term74 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0))).
Definition term73 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (num_of_int (int_mul (int_of_num x0) y1)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y1))) y0).
Definition term57 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1))).
Definition term56 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_mul y1 y2)) = (Nat.mul (num_of_int y1) (num_of_int y2))) y0).
Definition term41 (x0 : int) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0))).
Definition term40 (x0 : int) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul x0 y1)) = (Nat.mul (num_of_int x0) (num_of_int y1))) y0).
Definition term5 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term4 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term18 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term39 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul x0 y1)) = (Nat.mul (num_of_int x0) (num_of_int y1))) y0.
Definition term3 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term2 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term12 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term62 := forall y0 : nat, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul (int_of_num y0) y1)) = (Nat.mul (num_of_int (int_of_num y0)) (num_of_int y1)).
Definition term72 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0)).
Definition term34 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term69 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (fun y0 : int => (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0))) x1.
Definition term71 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (num_of_int (int_mul (int_of_num x0) y1)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y1))) y0.
Definition term1 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term27 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term86 := forall y0 : nat, True.
Definition term48 := forall y0 : int, forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1)).
Definition term76 (x0 : nat) (x1 : nat) := num_of_int (int_mul (int_of_num x0) (int_of_num x1)).
Definition term66 (x0 : nat) (x1 : int) := (fun y0 : int => (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0))) x1.
Definition term77 (x0 : nat) (x1 : nat) := Nat.mul (num_of_int (int_of_num x0)) (num_of_int (int_of_num x1)).
Definition term85 := fun y0 : nat => True.
Definition term79 (x0 : nat) := fun y0 : nat => (num_of_int (int_mul (int_of_num x0) (int_of_num y0))) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int (int_of_num y0))).
Definition term70 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (num_of_int (int_mul (int_of_num x0) x1)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int x1)).
Definition term36 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (num_of_int (int_mul x0 x1)) = (Nat.mul (num_of_int x0) (num_of_int x1)).
Definition term30 (x0 : Prop) (x1 : int -> Prop) := forall y0 : int, x0 -> x1 y0.
Definition term28 (x0 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0)).
Definition term9 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term35 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0))) x1.
Definition term60 := fun y0 : nat => (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_mul y1 y2)) = (Nat.mul (num_of_int y1) (num_of_int y2))) (int_of_num y0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term55 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_mul y1 y2)) = (Nat.mul (num_of_int y1) (num_of_int y2))) y0.
Definition term61 := fun y0 : nat => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul (int_of_num y0) y1)) = (Nat.mul (num_of_int (int_of_num y0)) (num_of_int y1)).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term54 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1))) x0.
Definition term7 (x0 : nat) := num_of_int (int_of_num x0).
Definition term0 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term64 (x0 : nat) := forall y0 : nat, (fun y1 : int => (num_of_int (int_mul (int_of_num x0) y1)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y1))) (int_of_num y0).
Definition term22 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (num_of_int (int_mul x0 x1)) = (Nat.mul (num_of_int x0) (num_of_int x1)).
Definition term84 (x0 : nat) := Nat.mul (num_of_int (int_of_num x0)).
Definition term49 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul y0 y1)) = (Nat.mul (num_of_int y0) (num_of_int y1)).
Definition term63 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (num_of_int (int_mul (int_of_num x0) y1)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y1))) y0.
Definition term50 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_mul y1 y2)) = (Nat.mul (num_of_int y1) (num_of_int y2))) y0.
Definition term32 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul x0 y1)) = (Nat.mul (num_of_int x0) (num_of_int y1))) y0.
Definition term31 (x0 : Prop) (x1 : int -> Prop) := x0 -> forall y0 : int, x1 y0.
Definition term83 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 x1).
Definition term88 (x0 : Prop) := forall y0 : nat, x0.
Definition term75 (x0 : nat) (x1 : nat) := (fun y0 : int => (num_of_int (int_mul (int_of_num x0) y0)) = (Nat.mul (num_of_int (int_of_num x0)) (num_of_int y0))) (int_of_num x1).
Definition term81 (x0 : nat) (x1 : nat) := num_of_int (int_of_num (Nat.mul x0 x1)).
Definition term23 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term51 := forall y0 : nat, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_mul y1 y2)) = (Nat.mul (num_of_int y1) (num_of_int y2))) (int_of_num y0).
Definition term38 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_mul x0 y0)) = (Nat.mul (num_of_int x0) (num_of_int y0))) x1.
Definition term6 (x0 : nat) := (fun y0 : nat => (num_of_int (int_of_num y0)) = y0) x0.
Definition term42 (x0 : int) := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul x0 y1)) = (Nat.mul (num_of_int x0) (num_of_int y1))) y0.
Definition term43 (x0 : int) := forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_mul x0 y1)) = (Nat.mul (num_of_int x0) (num_of_int y1))) y0.
Definition term24 (x0 : int) (x1 : int) := num_of_int (int_mul x0 x1).
Definition term11 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term21 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> (num_of_int (int_mul x0 x1)) = (Nat.mul (num_of_int x0) (num_of_int x1)).
