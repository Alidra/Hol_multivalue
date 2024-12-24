Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) \/ (Peano.lt x0 y0).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 \/ y1) = (y1 \/ y0)) x0.
Definition term10 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) \/ (Peano.lt y0 y1).
Definition term9 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term14 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term7 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 \/ y0) = (y0 \/ x0)) x1.
Definition term12 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) \/ (Peano.lt y0 y1).
Definition term11 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term4 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term6 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) \/ (Peano.lt x0 y0).
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term1 (x0 : Prop) := forall y0 : Prop, (x0 \/ y0) = (y0 \/ x0).
Definition term3 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
