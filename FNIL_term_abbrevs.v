Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') := @ε a0 (fun y0 : a0 => True).
Definition term0 (a0 : Type') := fun y0 : nat => @ε a0 (fun y1 : a0 => True).
Definition term4 (a0 : Type') (x0 : nat) := (fun y0 : nat => (@FNIL a0 y0) = (@ε a0 (fun y1 : a0 => True))) x0.
Definition term3 (a0 : Type') := forall y0 : nat, (@FNIL a0 y0) = (@ε a0 (fun y1 : a0 => True)).
Definition term1 (a0 : Type') (x0 : nat) := (fun y0 : nat => @ε a0 (fun y1 : a0 => True)) x0.
