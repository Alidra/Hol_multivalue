Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term42 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term35 := fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term71 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0)))).
Definition term40 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul x0 y0) = (int_of_num (NUMERAL (BIT1 0)))) = ((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term38 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term76 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term19 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term36 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term22 (x0 : int) := (fun y0 : int => forall y1 : int, (int_abs (int_mul y0 y1)) = (int_mul (int_abs y0) (int_abs y1))) x0.
Definition term54 (x0 : nat) (x1 : int) := (fun y0 : int => ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0)))))) x1.
Definition term81 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul (int_abs x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0)))))) (int_abs x1).
Definition term12 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term30 (x0 : int) (x1 : int) := @eq Prop ((int_abs (int_mul x0 x1)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : nat) := fun y0 : nat => (fun y1 : int => ((int_mul (int_of_num x0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num y0).
Definition term78 (x0 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) (int_abs x0).
Definition term20 (x0 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (int_abs y0)) x0.
Definition term55 (x0 : nat) (x1 : int) := int_mul (int_of_num x0) x1.
Definition term46 (x0 : nat) := (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num x0).
Definition term80 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul (int_abs x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term47 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term37 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul x0 y0) = (int_of_num (NUMERAL (BIT1 0)))) = ((x0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0))))) x1.
Definition term72 (x0 : nat) := and ((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term79 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) (int_abs x0)) -> forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul (int_abs x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term23 (x0 : int) := forall y0 : int, (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0)).
Definition term67 (x0 : nat) := forall y0 : nat, ((int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_of_num y0) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term7 (x0 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) /\ (y0 = (NUMERAL (BIT1 0)))).
Definition term10 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) /\ (x1 = (NUMERAL (BIT1 0))).
Definition term62 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0)))))).
Definition term61 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => ((int_mul (int_of_num x0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) y0).
Definition term45 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))).
Definition term44 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> ((int_mul y1 y2) = (int_of_num (NUMERAL (BIT1 0)))) = ((y1 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y2 = (int_of_num (NUMERAL (BIT1 0)))))) y0).
Definition term27 (x0 : int) (x1 : int) := @eq int (int_abs (int_mul x0 x1)).
Definition term26 (x0 : int) (x1 : int) := int_mul (int_abs x0) (int_abs x1).
Definition term5 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term4 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term60 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term3 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term2 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term18 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term50 := forall y0 : nat, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul (int_of_num y0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num y0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term25 (x0 : int) (x1 : int) := int_abs (int_mul x0 x1).
Definition term73 (x0 : nat) := and (x0 = (NUMERAL (BIT1 0))).
Definition term57 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (fun y0 : int => ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0)))))) x1.
Definition term83 (x0 : int) := forall y0 : int, ((int_abs (int_mul x0 y0)) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_abs y0) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term59 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => ((int_mul (int_of_num x0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term1 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term75 := forall y0 : nat, True.
Definition term66 (x0 : nat) := fun y0 : nat => ((int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_of_num y0) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term84 := forall y0 : int, forall y1 : int, ((int_abs (int_mul y0 y1)) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs y0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_abs y1) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term56 (x0 : nat) (x1 : int) := ((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : nat) (x1 : nat) := ((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_of_num x1) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term63 (x0 : nat) (x1 : nat) := (fun y0 : int => ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num x1).
Definition term74 := fun y0 : nat => True.
Definition term32 (x0 : int) (x1 : int) := ((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_abs x1) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term15 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term48 := fun y0 : nat => (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> ((int_mul y1 y2) = (int_of_num (NUMERAL (BIT1 0)))) = ((y1 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y2 = (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num y0).
Definition term41 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> ((int_mul y1 y2) = (int_of_num (NUMERAL (BIT1 0)))) = ((y1 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y2 = (int_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term49 := fun y0 : nat => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul (int_of_num y0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num y0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) /\ (y1 = (NUMERAL (BIT1 0))))) x0.
Definition term53 (x0 : nat) := fun y0 : int => ((int_mul (int_of_num x0) y0) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y0 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0))) x1.
Definition term39 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term0 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term52 (x0 : nat) := forall y0 : nat, (fun y1 : int => ((int_mul (int_of_num x0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num y0).
Definition term21 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_abs x0).
Definition term24 (x0 : int) (x1 : int) := (fun y0 : int => (int_abs (int_mul x0 y0)) = (int_mul (int_abs x0) (int_abs y0))) x1.
Definition term43 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> ((int_mul y0 y1) = (int_of_num (NUMERAL (BIT1 0)))) = ((y0 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term51 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => ((int_mul (int_of_num x0) y1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (y1 = (int_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term33 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> ((int_mul y1 y2) = (int_of_num (NUMERAL (BIT1 0)))) = ((y1 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y2 = (int_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term82 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) (int_abs x1)) -> ((int_mul (int_abs x0) (int_abs x1)) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_abs x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ ((int_abs x1) = (int_of_num (NUMERAL (BIT1 0))))).
Definition term70 (x0 : nat) (x1 : nat) := @eq Prop ((int_mul (int_of_num x0) (int_of_num x1)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : int) (x1 : int) := @eq Prop ((int_mul (int_abs x0) (int_abs x1)) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term77 (x0 : Prop) := forall y0 : nat, x0.
Definition term28 (x0 : int) (x1 : int) := @eq int (int_mul (int_abs x0) (int_abs x1)).
Definition term34 := forall y0 : nat, (fun y1 : int => forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y2) -> ((int_mul y1 y2) = (int_of_num (NUMERAL (BIT1 0)))) = ((y1 = (int_of_num (NUMERAL (BIT1 0)))) /\ (y2 = (int_of_num (NUMERAL (BIT1 0)))))) (int_of_num y0).
Definition term69 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.mul x0 x1)).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term58 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_mul (int_of_num x0) x1) = (int_of_num (NUMERAL (BIT1 0)))) = (((int_of_num x0) = (int_of_num (NUMERAL (BIT1 0)))) /\ (x1 = (int_of_num (NUMERAL (BIT1 0))))).
Definition term29 := int_of_num (NUMERAL (BIT1 0)).
Definition term17 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term9 := NUMERAL (BIT1 0).
Definition term68 (x0 : nat) (x1 : nat) := @eq int (int_mul (int_of_num x0) (int_of_num x1)).
