Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 (@INSERT a0 y1 y0)) = (@FINITE a0 y0)) x0.
Definition term9 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term8 (a0 : Type') := forall y0 : a0, True.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@FINITE a0 (@INSERT a0 y0 x0)) = (@FINITE a0 x0)) x1.
Definition term7 (a0 : Type') := forall y0 : a0, @FINITE a0 (@INSERT a0 y0 (@EMPTY a0)).
Definition term6 (a0 : Type') := fun y0 : a0 => True.
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term5 (a0 : Type') := fun y0 : a0 => @FINITE a0 (@INSERT a0 y0 (@EMPTY a0)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@FINITE a0 (@INSERT a0 y0 x0)) = (@FINITE a0 x0).
Definition term4 (a0 : Type') (x0 : a0) := @FINITE a0 (@INSERT a0 x0 (@EMPTY a0)).