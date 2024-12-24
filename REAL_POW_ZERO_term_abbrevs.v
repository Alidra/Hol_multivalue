Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : nat) := ((fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0) -> (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S x0).
Definition term22 (x0 : nat) := imp ((real_pow (real_of_num (NUMERAL 0)) x0) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : nat) := @COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term36 := fun y0 : nat => (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0.
Definition term14 := real_pow (real_of_num (NUMERAL 0)) (NUMERAL 0).
Definition term2 := real_of_num (NUMERAL 0).
Definition term12 := fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term6 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term46 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_pow (real_of_num (NUMERAL 0)) x0).
Definition term33 := ((real_pow (real_of_num (NUMERAL 0)) (NUMERAL 0)) = (@COND real ((NUMERAL 0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> (real_pow (real_of_num (NUMERAL 0)) (S y0)) = (@COND real ((S y0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term9 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term37 := forall y0 : nat, (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0.
Definition term32 := ((fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S y0)).
Definition term8 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term7 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term11 := (((fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0.
Definition term40 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term10 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term13 := (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (NUMERAL 0).
Definition term34 := imp (((fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S y0))).
Definition term25 (x0 : nat) := @COND real ((S x0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term15 := @COND real ((NUMERAL 0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term47 (x0 : nat) := @eq real (real_pow (real_of_num (NUMERAL 0)) (S x0)).
Definition term49 (x0 : nat) := @COND real ((S x0) = (NUMERAL 0)).
Definition term23 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S x0).
Definition term30 := forall y0 : nat, ((fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S y0).
Definition term52 := @COND real False (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term16 := and ((fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (NUMERAL 0)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term27 (x0 : nat) := ((real_pow (real_of_num (NUMERAL 0)) x0) = (@COND real (x0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> (real_pow (real_of_num (NUMERAL 0)) (S x0)) = (@COND real ((S x0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term28 := fun y0 : nat => ((fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) y0) -> (fun y1 : nat => (real_pow (real_of_num (NUMERAL 0)) y1) = (@COND real (y1 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) (S y0).
Definition term48 := @eq real (real_of_num (NUMERAL 0)).
Definition term38 := forall y0 : nat, (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term18 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0.
Definition term39 := (((real_pow (real_of_num (NUMERAL 0)) (NUMERAL 0)) = (@COND real ((NUMERAL 0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> (real_pow (real_of_num (NUMERAL 0)) (S y0)) = (@COND real ((S y0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))) -> forall y0 : nat, (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term4 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term29 := fun y0 : nat => ((real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> (real_pow (real_of_num (NUMERAL 0)) (S y0)) = (@COND real ((S y0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term24 (x0 : nat) := real_pow (real_of_num (NUMERAL 0)) (S x0).
Definition term3 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term42 := @eq real (real_pow (real_of_num (NUMERAL 0)) (NUMERAL 0)).
Definition term41 := real_of_num (NUMERAL (BIT1 0)).
Definition term51 := @COND real False (real_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term1 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term50 (x0 : nat) := @COND real ((S x0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term35 := imp (((real_pow (real_of_num (NUMERAL 0)) (NUMERAL 0)) = (@COND real ((NUMERAL 0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) /\ (forall y0 : nat, ((real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> (real_pow (real_of_num (NUMERAL 0)) (S y0)) = (@COND real ((S y0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))).
Definition term45 (x0 : nat) (x1 : real) (x2 : real) := @COND real (x0 = x0) x1 x2.
Definition term43 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term31 := forall y0 : nat, ((real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) -> (real_pow (real_of_num (NUMERAL 0)) (S y0)) = (@COND real ((S y0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term19 (x0 : nat) := real_pow (real_of_num (NUMERAL 0)) x0.
Definition term21 (x0 : nat) := imp ((fun y0 : nat => (real_pow (real_of_num (NUMERAL 0)) y0) = (@COND real (y0 = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))) x0).
Definition term17 := and ((real_pow (real_of_num (NUMERAL 0)) (NUMERAL 0)) = (@COND real ((NUMERAL 0) = (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
