Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0) := fun y0 : unit => x0.
Definition term3 (a0 : Type') (x0 : a0) := fun y0 : unit -> a0 => (y0 tt) = x0.
Definition term1 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : unit => x0) tt).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : unit => x0) tt.
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : unit -> a0, (y0 tt) = x0.
Definition term5 (a0 : Type') := forall y0 : a0, exists y1 : unit -> a0, (y1 tt) = y0.
