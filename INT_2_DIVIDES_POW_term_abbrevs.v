Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term72 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term81 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term56 := ((int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL (BIT1 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term87 := @eq int (int_of_num (NUMERAL (BIT1 0))).
Definition term62 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term4 := fun y0 : int => ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term38 (x0 : int) := fun y0 : nat => (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term50 (x0 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term65 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term57 := int_of_num (NUMERAL 0).
Definition term16 (x0 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (NUMERAL 0)).
Definition term17 (x0 : int) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term108 (x0 : nat) (x1 : int) := @eq Prop (((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) \/ ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1) /\ (~ (x0 = (NUMERAL 0))))) = (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1)).
Definition term91 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul y0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y1))) x0.
Definition term110 (x0 : nat) := False \/ (False /\ (~ (x0 = (NUMERAL 0)))).
Definition term14 (x0 : int) := fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0)))).
Definition term8 (x0 : int) := forall y0 : nat, (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0)).
Definition term85 := ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term103 (x0 : nat) := fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0.
Definition term104 (x0 : nat) (x1 : int) := (fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term35 (x0 : int) := ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (NUMERAL 0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) -> (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S y0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S y0) = (NUMERAL 0))))).
Definition term39 (x0 : int) := forall y0 : nat, (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term34 (x0 : int) := ((fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0)).
Definition term75 := (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0))) x1.
Definition term5 := fun y0 : int => (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term66 := int_of_num (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term28 (x0 : int) (x1 : nat) := ((fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) x1) -> (fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term13 (x0 : int) := (((fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0.
Definition term111 (x0 : nat) := True /\ (~ (x0 = (NUMERAL 0))).
Definition term109 (x0 : nat) := (fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) False.
Definition term69 := Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term12 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term86 := @eq int (rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term77 := int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term36 (x0 : int) := imp (((fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0))).
Definition term74 := Nat.add (BIT1 0) 0.
Definition term48 (x0 : int) := and (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term100 (x0 : int) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ True.
Definition term47 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term55 := rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term95 (x0 : int) (x1 : int) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term70 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) -> (int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0)))))) -> ((div (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL 0))) /\ ((rem (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term11 (x0 : int) (x1 : nat) := int_mul x0 (int_pow x0 x1).
Definition term32 (x0 : int) := forall y0 : nat, ((fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term114 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term43 := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term64 := int_add (int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term92 (x0 : int) := forall y0 : int, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term44 := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0))).
Definition term52 (x0 : int) (x1 : nat) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 (int_pow x0 x1)).
Definition term18 (x0 : int) := and ((fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0)).
Definition term107 (x0 : nat) (x1 : int) := @eq Prop ((fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x1)).
Definition term46 := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term73 := Peano.le (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term3 (x0 : int) := ~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term63 := int_add (int_of_num (NUMERAL 0)).
Definition term30 (x0 : int) := fun y0 : nat => ((fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) y0) -> (fun y1 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y1 = (NUMERAL 0))))) (S y0).
Definition term98 (x0 : int) (x1 : nat) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (x1 = (NUMERAL 0)))).
Definition term21 (x0 : int) (x1 : nat) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 x1).
Definition term51 := ~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term0 := forall y0 : int, ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))) = (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)).
Definition term59 (x0 : nat) := int_mul (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term94 (x0 : int) (x1 : int) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 x1).
Definition term41 (x0 : int) := (((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (NUMERAL 0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) -> (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S y0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S y0) = (NUMERAL 0)))))) -> forall y0 : nat, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0)))).
Definition term101 (x0 : int) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term42 (x0 : int) := int_pow x0 (NUMERAL 0).
Definition term53 (x0 : int) (x1 : nat) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S x1))).
Definition term115 := forall y0 : int, forall y1 : nat, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow y0 y1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0) /\ (~ (y1 = (NUMERAL 0)))).
Definition term23 (x0 : int) (x1 : nat) := imp ((fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) x1).
Definition term9 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0))) x1.
Definition term1 (x0 : int) := rem x0 (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term80 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term76 (x0 : nat) := int_abs (int_of_num x0).
Definition term78 := int_lt (int_of_num (NUMERAL (BIT1 0))).
Definition term24 (x0 : int) (x1 : nat) := imp ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 x1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (x1 = (NUMERAL 0))))).
Definition term26 (x0 : int) (x1 : nat) := int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S x1)).
Definition term89 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term60 := int_mul (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term79 := int_lt (int_of_num (NUMERAL (BIT1 0))) (int_abs (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term82 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term10 (x0 : int) (x1 : nat) := int_pow x0 (S x1).
Definition term96 (x0 : int) (x1 : nat) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 x1)).
Definition term61 := NUMERAL (BIT0 (BIT1 0)).
Definition term27 (x0 : int) (x1 : nat) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S x1) = (NUMERAL 0))).
Definition term97 (x0 : int) := or (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term31 (x0 : int) := fun y0 : nat => ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) -> (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S y0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term112 (x0 : nat) := ~ (False \/ (False /\ (~ (x0 = (NUMERAL 0))))).
Definition term20 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term19 (x0 : int) := and ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (NUMERAL 0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))).
Definition term54 (x0 : int) (x1 : nat) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_mul x0 (int_pow x0 x1))).
Definition term88 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term45 (x0 : int) := @eq Prop (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (NUMERAL 0))).
Definition term58 := int_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term68 := Nat.add 0 (BIT1 0).
Definition term84 := BIT0 (BIT1 0).
Definition term102 (x0 : int) := ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = True) \/ ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = False).
Definition term90 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term99 (x0 : int) (x1 : nat) := @eq Prop ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) \/ ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (x1 = (NUMERAL 0))))).
Definition term37 (x0 : int) := imp (((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (NUMERAL 0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((NUMERAL 0) = (NUMERAL 0))))) /\ (forall y0 : nat, ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) -> (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S y0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S y0) = (NUMERAL 0)))))).
Definition term71 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term33 (x0 : int) := forall y0 : nat, ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) -> (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S y0))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S y0) = (NUMERAL 0)))).
Definition term29 (x0 : int) (x1 : nat) := ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 x1)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (x1 = (NUMERAL 0))))) -> (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 (S x1))) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ ((S x1) = (NUMERAL 0)))).
Definition term25 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (S x1).
Definition term15 (x0 : int) := (fun y0 : nat => (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0))))) (NUMERAL 0).
Definition term105 (x0 : nat) := (fun y0 : Prop => (y0 \/ (y0 /\ (~ (x0 = (NUMERAL 0))))) = y0) True.
Definition term7 (x0 : int) := (fun y0 : int => (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0))))) x0.
Definition term106 (x0 : nat) := True \/ (True /\ (~ (x0 = (NUMERAL 0)))).
Definition term83 := S (Nat.add 0 (BIT1 0)).
Definition term49 (x0 : int) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ False.
Definition term22 (x0 : int) (x1 : nat) := (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (x1 = (NUMERAL 0))).
Definition term2 := int_of_num (NUMERAL (BIT1 0)).
Definition term6 := forall y0 : int, (~ (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = ((rem y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (int_of_num (NUMERAL (BIT1 0)))).
Definition term113 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term67 := NUMERAL (BIT1 0).
Definition term40 (x0 : int) := forall y0 : nat, (int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_pow x0 y0)) = ((int_divides (int_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) /\ (~ (y0 = (NUMERAL 0)))).
