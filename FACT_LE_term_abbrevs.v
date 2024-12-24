Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 := S (NUMERAL 0).
Definition term1 (x0 : nat) := Peano.lt (NUMERAL 0) (Factorial.fact x0).
Definition term10 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) (Factorial.fact x0).
Definition term3 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term12 := fun y0 : nat => Peano.le (NUMERAL (BIT1 0)) (Factorial.fact y0).
Definition term14 := forall y0 : nat, Peano.le (NUMERAL (BIT1 0)) (Factorial.fact y0).
Definition term15 := forall y0 : nat, True.
Definition term13 := fun y0 : nat => True.
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) x0.
Definition term9 := Peano.le (S (NUMERAL 0)).
Definition term5 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term17 (x0 : Prop) := forall y0 : nat, x0.
Definition term11 (x0 : nat) := Peano.le (S (NUMERAL 0)) (Factorial.fact x0).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) x0.
Definition term6 := NUMERAL (BIT1 0).
Definition term8 := Peano.le (NUMERAL (BIT1 0)).
