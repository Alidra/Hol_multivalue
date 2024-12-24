Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 := forall y0 : real, (real_zpow y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (real_mul y0 y0).
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term11 := fun y0 : real => True.
Definition term3 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term0 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) x0.
Definition term13 := forall y0 : real, True.
Definition term15 (x0 : Prop) := forall y0 : real, x0.
Definition term9 (x0 : real) := @eq real (real_mul x0 x0).
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term1 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term6 (x0 : real) := real_zpow x0 (int_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term8 (x0 : real) := @eq real (real_zpow x0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term7 := NUMERAL (BIT0 (BIT1 0)).
Definition term10 := fun y0 : real => (real_zpow y0 (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (real_mul y0 y0).
Definition term4 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term5 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
