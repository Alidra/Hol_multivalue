Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term5 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = (Peano.le x0 y0).
Definition term9 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (S x0) (S x1)).
Definition term17 := fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1).
Definition term10 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term1 (x0 : nat) := forall y0 : nat, (Peano.le (S x0) y0) = (Peano.lt x0 y0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (S x0) y0) = (Peano.lt x0 y0)) x1.
Definition term18 := forall y0 : nat, forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = (Peano.le x0 y0)) x1.
Definition term7 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term14 := forall y0 : nat, True.
Definition term11 (x0 : nat) := fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term12 := fun y0 : nat => True.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = (Peano.le y0 y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (S y0) y1) = (Peano.lt y0 y1)) x0.
Definition term8 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term16 (x0 : Prop) := forall y0 : nat, x0.
