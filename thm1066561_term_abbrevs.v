Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2).
Definition term3 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : nat, (@FCONS a0 x0 y0 (S y1)) = (y0 y1)) x1.
Definition term5 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (@FCONS a0 x0 x1 (S y0)) = (x1 y0)) x2.
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : nat -> a0, forall y1 : nat, (@FCONS a0 x0 y0 (S y1)) = (y0 y1).
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : nat -> a0, forall y2 : nat, (@FCONS a0 y0 y1 (S y2)) = (y1 y2)) x0.
Definition term4 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := forall y0 : nat, (@FCONS a0 x0 x1 (S y0)) = (x1 y0).
