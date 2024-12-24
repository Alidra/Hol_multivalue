Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : nat, (@dollar a0 a1 x0 y0) = (@dest_cart a0 a1 x0 (@finite_index a1 y0)).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => fun y1 : nat => @dest_cart a0 a1 y0 (@finite_index a1 y1).
Definition term6 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, forall y1 : nat, (@dollar a0 a1 y0 y1) = (@dest_cart a0 a1 y0 (@finite_index a1 y1)).
Definition term1 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => fun y1 : nat => @dest_cart a0 a1 y0 (@finite_index a1 y1)) x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := (fun y0 : nat => @dest_cart a0 a1 x0 (@finite_index a1 y0)) x1.
Definition term4 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @dest_cart a0 a1 x0 (@finite_index a1 x1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => forall y1 : nat, (@dollar a0 a1 y0 y1) = (@dest_cart a0 a1 y0 (@finite_index a1 y1))) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : nat => @dest_cart a0 a1 x0 (@finite_index a1 y0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := (fun y0 : nat => (@dollar a0 a1 x0 y0) = (@dest_cart a0 a1 x0 (@finite_index a1 y0))) x1.
