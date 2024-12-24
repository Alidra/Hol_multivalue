Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0.
Definition term58 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.mul x0 (Nat.pow x0 x1))).
Definition term49 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term45 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term17 (x0 : nat) (x1 : nat) := ((real_pow (real_of_num x0) x1) = (real_of_num (Nat.pow x0 x1))) -> (real_pow (real_of_num x0) (S x1)) = (real_of_num (Nat.pow x0 (S x1))).
Definition term52 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term27 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0.
Definition term22 (x0 : nat) := ((fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0) -> (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) (S y0)).
Definition term51 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term50 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term47 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term16 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) x1) -> (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (S x1).
Definition term1 (x0 : nat) := (((fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0) -> (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0.
Definition term46 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term34 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term32 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term10 (x0 : nat) (x1 : nat) := real_of_num (Nat.pow x0 x1).
Definition term24 (x0 : nat) := imp (((fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0) -> (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) (S y0))).
Definition term3 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (NUMERAL 0).
Definition term20 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0) -> (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) (S y0).
Definition term19 (x0 : nat) := fun y0 : nat => ((real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) -> (real_pow (real_of_num x0) (S y0)) = (real_of_num (Nat.pow x0 (S y0))).
Definition term40 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0))) x1.
Definition term6 (x0 : nat) := and ((fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (NUMERAL 0)).
Definition term14 (x0 : nat) (x1 : nat) := real_pow (real_of_num x0) (S x1).
Definition term36 (x0 : nat) := @eq real (real_pow (real_of_num x0) (NUMERAL 0)).
Definition term56 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 (Nat.pow x0 x1)).
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term18 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) y0) -> (fun y1 : nat => (real_pow (real_of_num x0) y1) = (real_of_num (Nat.pow x0 y1))) (S y0).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) x1.
Definition term7 (x0 : nat) := and ((real_pow (real_of_num x0) (NUMERAL 0)) = (real_of_num (Nat.pow x0 (NUMERAL 0)))).
Definition term59 := forall y0 : nat, forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1)).
Definition term43 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term53 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_pow (real_of_num x0) x1).
Definition term48 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term11 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) x1).
Definition term15 (x0 : nat) (x1 : nat) := real_of_num (Nat.pow x0 (S x1)).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) (S x1).
Definition term54 (x0 : nat) := real_mul (real_of_num x0).
Definition term41 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term57 (x0 : nat) (x1 : nat) := @eq real (real_pow (real_of_num x0) (S x1)).
Definition term5 (x0 : nat) := real_of_num (Nat.pow x0 (NUMERAL 0)).
Definition term23 (x0 : nat) := ((real_pow (real_of_num x0) (NUMERAL 0)) = (real_of_num (Nat.pow x0 (NUMERAL 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) -> (real_pow (real_of_num x0) (S y0)) = (real_of_num (Nat.pow x0 (S y0)))).
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term38 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_mul (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.mul y0 y1))) x0.
Definition term30 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term12 (x0 : nat) (x1 : nat) := imp ((real_pow (real_of_num x0) x1) = (real_of_num (Nat.pow x0 x1))).
Definition term2 (x0 : nat) := fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term39 (x0 : nat) := forall y0 : nat, (real_mul (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.mul x0 y0)).
Definition term35 := real_of_num (NUMERAL (BIT1 0)).
Definition term28 (x0 : nat) := forall y0 : nat, (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term9 (x0 : nat) (x1 : nat) := real_pow (real_of_num x0) x1.
Definition term37 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term42 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term4 (x0 : nat) := real_pow (real_of_num x0) (NUMERAL 0).
Definition term21 (x0 : nat) := forall y0 : nat, ((real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) -> (real_pow (real_of_num x0) (S y0)) = (real_of_num (Nat.pow x0 (S y0))).
Definition term29 (x0 : nat) := (((real_pow (real_of_num x0) (NUMERAL 0)) = (real_of_num (Nat.pow x0 (NUMERAL 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) -> (real_pow (real_of_num x0) (S y0)) = (real_of_num (Nat.pow x0 (S y0))))) -> forall y0 : nat, (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term33 := NUMERAL (BIT1 0).
Definition term25 (x0 : nat) := imp (((real_pow (real_of_num x0) (NUMERAL 0)) = (real_of_num (Nat.pow x0 (NUMERAL 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) -> (real_pow (real_of_num x0) (S y0)) = (real_of_num (Nat.pow x0 (S y0))))).
Definition term55 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num (Nat.pow x0 x1)).
