Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term9 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (S x0) x1.
Definition term2 := fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term3 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term10 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 x0 (@tl a0 x1).
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0)) x0.
Definition term11 (a0 : Type') (x0 : nat) (x1 : list a0) := @eq a0 (@EL a0 x0 (@tl a0 x1)).
Definition term14 (a0 : Type') (x0 : list a0) := forall y0 : nat, (@EL a0 y0 (@tl a0 x0)) = (@EL a0 (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term8 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term15 := forall y0 : nat, True.
Definition term0 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term13 := fun y0 : nat => True.
Definition term12 (a0 : Type') (x0 : list a0) := fun y0 : nat => (@EL a0 y0 (@tl a0 x0)) = (@EL a0 (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term7 (a0 : Type') (x0 : nat) := @EL a0 (S x0).
Definition term17 (x0 : Prop) := forall y0 : nat, x0.
Definition term4 := forall y0 : nat, (Nat.add y0 (NUMERAL (BIT1 0))) = (S y0).
Definition term1 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term6 (a0 : Type') (x0 : nat) := @EL a0 (Nat.add x0 (NUMERAL (BIT1 0))).
