Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := (fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0)))) x0.
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (x0 : nat) := real_of_num (S x0).
Definition term3 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term7 (x0 : nat) := real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term16 := forall y0 : nat, True.
Definition term6 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term14 := fun y0 : nat => True.
Definition term15 := forall y0 : nat, (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (S y0)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term11 (x0 : nat) := @eq real (real_of_num (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term1 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term8 (x0 : nat) := real_of_num (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term10 (x0 : nat) := @eq real (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term18 (x0 : Prop) := forall y0 : nat, x0.
Definition term13 := fun y0 : nat => (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (S y0)).
Definition term4 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term9 := NUMERAL (BIT1 0).
