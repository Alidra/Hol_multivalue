Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_of_real (real_pow (real_of_int x0) x1))).
Definition term9 (x0 : nat) := int_of_real (real_of_num x0).
Definition term0 (x0 : int) (x1 : int) := int_of_real (real_mul (real_of_int x0) (real_of_int x1)).
Definition term44 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (S x1).
Definition term50 (x0 : int) := fun y0 : nat => ((real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) -> (real_of_int (int_of_real (real_pow (real_of_int x0) (S y0)))) = (real_pow (real_of_int x0) (S y0)).
Definition term95 (x0 : int) (x1 : nat) := @eq real (real_mul (real_of_int x0) (real_of_int (int_of_real (real_pow (real_of_int x0) x1)))).
Definition term43 (x0 : int) (x1 : nat) := imp ((real_of_int (int_of_real (real_pow (real_of_int x0) x1))) = (real_pow (real_of_int x0) x1)).
Definition term88 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term90 (x0 : int) (x1 : int) := (fun y0 : int => (int_of_real (real_mul (real_of_int x0) (real_of_int y0))) = (int_mul x0 y0)) x1.
Definition term40 (x0 : int) := and ((real_of_int (int_of_real (real_pow (real_of_int x0) (NUMERAL 0)))) = (real_pow (real_of_int x0) (NUMERAL 0))).
Definition term91 (x0 : int) (x1 : nat) := int_of_real (real_mul (real_of_int x0) (real_of_int (int_of_real (real_pow (real_of_int x0) x1)))).
Definition term89 (x0 : int) := (fun y0 : int => forall y1 : int, (int_of_real (real_mul (real_of_int y0) (real_of_int y1))) = (int_mul y0 y1)) x0.
Definition term84 (x0 : int) := (fun y0 : int => forall y1 : int, (real_of_int (int_mul y0 y1)) = (real_mul (real_of_int y0) (real_of_int y1))) x0.
Definition term17 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term21 (x0 : int) := (fun y0 : int => forall y1 : nat, (int_pow y0 y1) = (int_of_real (real_pow (real_of_int y0) y1))) x0.
Definition term20 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term58 (x0 : int) := forall y0 : nat, (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0.
Definition term53 (x0 : int) := ((fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0) -> (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) (S y0)).
Definition term19 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term4 (x0 : int) := forall y0 : int, (int_of_real (real_mul (real_of_int x0) (real_of_int y0))) = (int_mul x0 y0).
Definition term54 (x0 : int) := ((real_of_int (int_of_real (real_pow (real_of_int x0) (NUMERAL 0)))) = (real_pow (real_of_int x0) (NUMERAL 0))) /\ (forall y0 : nat, ((real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) -> (real_of_int (int_of_real (real_pow (real_of_int x0) (S y0)))) = (real_pow (real_of_int x0) (S y0))).
Definition term3 (x0 : int) := forall y0 : int, (int_mul x0 y0) = (int_of_real (real_mul (real_of_int x0) (real_of_int y0))).
Definition term18 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term82 (x0 : int) (x1 : nat) := @eq Prop ((fun y0 : real => (real_of_int (int_of_real (real_mul (real_of_int x0) y0))) = (real_mul (real_of_int x0) y0)) (real_pow (real_of_int x0) x1)).
Definition term47 (x0 : int) (x1 : nat) := ((fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) x1) -> (fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (S x1).
Definition term35 (x0 : int) := (((fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0) -> (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0.
Definition term77 (x0 : int) := fun y0 : real => (real_of_int (int_of_real (real_mul (real_of_int x0) y0))) = (real_mul (real_of_int x0) y0).
Definition term60 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term34 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term70 (x0 : int) (x1 : nat) := real_of_int (int_of_real (real_mul (real_of_int x0) (real_pow (real_of_int x0) x1))).
Definition term13 := forall y0 : nat, (int_of_real (real_of_num y0)) = (int_of_num y0).
Definition term55 (x0 : int) := imp (((fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0) -> (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) (S y0))).
Definition term62 (x0 : int) := int_of_real (real_pow (real_of_int x0) (NUMERAL 0)).
Definition term78 (x0 : int) (x1 : nat) := (fun y0 : real => (real_of_int (int_of_real (real_mul (real_of_int x0) y0))) = (real_mul (real_of_int x0) y0)) (real_pow (real_of_int x0) x1).
Definition term85 (x0 : int) := forall y0 : int, (real_of_int (int_mul x0 y0)) = (real_mul (real_of_int x0) (real_of_int y0)).
Definition term30 (x0 : int) := fun y0 : nat => (real_of_int (int_pow x0 y0)) = (real_pow (real_of_int x0) y0).
Definition term5 := fun y0 : int => forall y1 : int, (int_mul y0 y1) = (int_of_real (real_mul (real_of_int y0) (real_of_int y1))).
Definition term51 (x0 : int) := forall y0 : nat, ((fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0) -> (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) (S y0).
Definition term12 := forall y0 : nat, (int_of_num y0) = (int_of_real (real_of_num y0)).
Definition term10 := fun y0 : nat => (int_of_num y0) = (int_of_real (real_of_num y0)).
Definition term46 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) (S x1).
Definition term39 (x0 : int) := and ((fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (NUMERAL 0)).
Definition term15 (x0 : nat) := real_of_int (int_of_num x0).
Definition term83 (x0 : int) (x1 : nat) := @eq Prop ((real_of_int (int_of_real (real_mul (real_of_int x0) (real_pow (real_of_int x0) x1)))) = (real_mul (real_of_int x0) (real_pow (real_of_int x0) x1))).
Definition term49 (x0 : int) := fun y0 : nat => ((fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0) -> (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) (S y0).
Definition term1 (x0 : int) := fun y0 : int => (int_mul x0 y0) = (int_of_real (real_mul (real_of_int x0) (real_of_int y0))).
Definition term26 (x0 : int) (x1 : nat) := real_of_int (int_of_real (real_pow (real_of_int x0) x1)).
Definition term14 (x0 : nat) := (fun y0 : nat => (real_of_int (int_of_num y0)) = (real_of_num y0)) x0.
Definition term79 (x0 : int) (x1 : nat) := (fun y0 : real => (real_of_int (int_of_real (real_mul (real_of_int x0) y0))) = (real_mul (real_of_int x0) y0)) (real_of_int (int_of_real (real_pow (real_of_int x0) x1))).
Definition term38 (x0 : int) := real_pow (real_of_int x0) (NUMERAL 0).
Definition term96 := forall y0 : int, forall y1 : nat, (real_of_int (int_pow y0 y1)) = (real_pow (real_of_int y0) y1).
Definition term8 := forall y0 : int, forall y1 : int, (int_of_real (real_mul (real_of_int y0) (real_of_int y1))) = (int_mul y0 y1).
Definition term7 := forall y0 : int, forall y1 : int, (int_mul y0 y1) = (int_of_real (real_mul (real_of_int y0) (real_of_int y1))).
Definition term42 (x0 : int) (x1 : nat) := imp ((fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) x1).
Definition term29 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term63 := int_of_real (real_of_num (NUMERAL (BIT1 0))).
Definition term59 (x0 : int) := (((real_of_int (int_of_real (real_pow (real_of_int x0) (NUMERAL 0)))) = (real_pow (real_of_int x0) (NUMERAL 0))) /\ (forall y0 : nat, ((real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) -> (real_of_int (int_of_real (real_pow (real_of_int x0) (S y0)))) = (real_pow (real_of_int x0) (S y0)))) -> forall y0 : nat, (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0).
Definition term6 := fun y0 : int => forall y1 : int, (int_of_real (real_mul (real_of_int y0) (real_of_int y1))) = (int_mul y0 y1).
Definition term93 (x0 : int) (x1 : nat) := real_of_int (int_mul x0 (int_of_real (real_pow (real_of_int x0) x1))).
Definition term31 (x0 : int) := fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0).
Definition term2 (x0 : int) := fun y0 : int => (int_of_real (real_mul (real_of_int x0) (real_of_int y0))) = (int_mul x0 y0).
Definition term64 := real_of_int (int_of_real (real_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : nat) := (fun y0 : nat => (int_of_real (real_of_num y0)) = (int_of_num y0)) x0.
Definition term45 (x0 : int) (x1 : nat) := real_of_int (int_of_real (real_pow (real_of_int x0) (S x1))).
Definition term71 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_of_real (real_pow (real_of_int x0) (S x1)))).
Definition term61 := real_of_num (NUMERAL (BIT1 0)).
Definition term48 (x0 : int) (x1 : nat) := ((real_of_int (int_of_real (real_pow (real_of_int x0) x1))) = (real_pow (real_of_int x0) x1)) -> (real_of_int (int_of_real (real_pow (real_of_int x0) (S x1)))) = (real_pow (real_of_int x0) (S x1)).
Definition term80 (x0 : int) (x1 : nat) := real_of_int (int_of_real (real_mul (real_of_int x0) (real_of_int (int_of_real (real_pow (real_of_int x0) x1))))).
Definition term27 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow x0 x1)).
Definition term56 (x0 : int) := imp (((real_of_int (int_of_real (real_pow (real_of_int x0) (NUMERAL 0)))) = (real_pow (real_of_int x0) (NUMERAL 0))) /\ (forall y0 : nat, ((real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) -> (real_of_int (int_of_real (real_pow (real_of_int x0) (S y0)))) = (real_pow (real_of_int x0) (S y0)))).
Definition term69 (x0 : int) (x1 : nat) := int_of_real (real_mul (real_of_int x0) (real_pow (real_of_int x0) x1)).
Definition term33 (x0 : int) := forall y0 : nat, (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0).
Definition term32 (x0 : int) := forall y0 : nat, (real_of_int (int_pow x0 y0)) = (real_pow (real_of_int x0) y0).
Definition term87 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term57 (x0 : int) := fun y0 : nat => (fun y1 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y1))) = (real_pow (real_of_int x0) y1)) y0.
Definition term11 := fun y0 : nat => (int_of_real (real_of_num y0)) = (int_of_num y0).
Definition term81 (x0 : int) (x1 : nat) := real_mul (real_of_int x0) (real_of_int (int_of_real (real_pow (real_of_int x0) x1))).
Definition term75 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term86 (x0 : int) (x1 : int) := (fun y0 : int => (real_of_int (int_mul x0 y0)) = (real_mul (real_of_int x0) (real_of_int y0))) x1.
Definition term76 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term68 (x0 : int) (x1 : nat) := int_of_real (real_pow (real_of_int x0) (S x1)).
Definition term66 := @eq real (real_of_int (int_of_real (real_of_num (NUMERAL (BIT1 0))))).
Definition term94 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_of_real (real_mul (real_of_int x0) (real_of_int (int_of_real (real_pow (real_of_int x0) x1)))))).
Definition term23 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_pow x0 y0) = (int_of_real (real_pow (real_of_int x0) y0))) x1.
Definition term52 (x0 : int) := forall y0 : nat, ((real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) -> (real_of_int (int_of_real (real_pow (real_of_int x0) (S y0)))) = (real_pow (real_of_int x0) (S y0)).
Definition term92 (x0 : int) (x1 : nat) := int_mul x0 (int_of_real (real_pow (real_of_int x0) x1)).
Definition term25 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term65 (x0 : int) := @eq real (real_of_int (int_of_real (real_pow (real_of_int x0) (NUMERAL 0)))).
Definition term22 (x0 : int) := forall y0 : nat, (int_pow x0 y0) = (int_of_real (real_pow (real_of_int x0) y0)).
Definition term24 (x0 : int) (x1 : nat) := int_of_real (real_pow (real_of_int x0) x1).
Definition term41 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) x1.
Definition term72 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_of_real (real_mul (real_of_int x0) (real_pow (real_of_int x0) x1)))).
Definition term37 (x0 : int) := real_of_int (int_of_real (real_pow (real_of_int x0) (NUMERAL 0))).
Definition term73 := int_of_num (NUMERAL (BIT1 0)).
Definition term67 (x0 : int) (x1 : nat) := real_mul (real_of_int x0) (real_pow (real_of_int x0) x1).
Definition term74 := NUMERAL (BIT1 0).
Definition term36 (x0 : int) := (fun y0 : nat => (real_of_int (int_of_real (real_pow (real_of_int x0) y0))) = (real_pow (real_of_int x0) y0)) (NUMERAL 0).
