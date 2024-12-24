Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : nat => fun y1 : nat => Peano.le y1 y0.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 x0) x1.
Definition term1 (x0 : nat) := (fun y0 : nat => fun y1 : nat => Peano.le y1 y0) x0.
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.ge y0 x0) = (Peano.le x0 y0).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.ge y1 y0) = (Peano.le y0 y1).
Definition term5 := forall y0 : nat, forall y1 : nat, (Peano.ge y0 y1) = (Peano.le y1 y0).
Definition term2 (x0 : nat) := fun y0 : nat => Peano.le y0 x0.
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.ge x0 y0) = (Peano.le y0 x0).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.ge x0 y0) = (Peano.le y0 x0)) x1.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.ge y0 y1) = (Peano.le y1 y0)) x0.
