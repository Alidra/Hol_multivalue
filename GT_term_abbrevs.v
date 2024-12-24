Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => fun y1 : nat => Peano.lt y1 y0) x0.
Definition term2 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.gt y0 x0) = (Peano.lt x0 y0).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.gt y1 y0) = (Peano.lt y0 y1).
Definition term5 := forall y0 : nat, forall y1 : nat, (Peano.gt y0 y1) = (Peano.lt y1 y0).
Definition term0 := fun y0 : nat => fun y1 : nat => Peano.lt y1 y0.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.gt x0 y0) = (Peano.lt y0 x0).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.gt x0 y0) = (Peano.lt y0 x0)) x1.
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.gt y0 y1) = (Peano.lt y1 y0)) x0.
