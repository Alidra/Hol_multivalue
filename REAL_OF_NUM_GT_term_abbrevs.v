Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term13 (x0 : nat) := fun y0 : nat => (real_gt (real_of_num x0) (real_of_num y0)) = (Peano.gt x0 y0).
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt y0 x0) = (real_lt x0 y0)) x1.
Definition term15 (x0 : nat) := forall y0 : nat, (real_gt (real_of_num x0) (real_of_num y0)) = (Peano.gt x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0).
Definition term11 (x0 : nat) (x1 : nat) := @eq Prop (real_gt (real_of_num x0) (real_of_num x1)).
Definition term5 (x0 : real) := forall y0 : real, (real_gt y0 x0) = (real_lt x0 y0).
Definition term19 := fun y0 : nat => forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1).
Definition term12 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term8 (x0 : nat) := forall y0 : nat, (Peano.gt y0 x0) = (Peano.lt x0 y0).
Definition term20 := forall y0 : nat, forall y1 : nat, (real_gt (real_of_num y0) (real_of_num y1)) = (Peano.gt y0 y1).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.gt y0 x0) = (Peano.lt x0 y0)) x1.
Definition term16 := forall y0 : nat, True.
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1)) x0.
Definition term10 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term14 := fun y0 : nat => True.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.gt y1 y0) = (Peano.lt y0 y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term18 (x0 : Prop) := forall y0 : nat, x0.
