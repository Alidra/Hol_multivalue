Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2.
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ ((~ (x0 = x1)) -> ((x0 = x1) \/ x2) -> x2)) -> False.
