Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@List.In a0 y0 (@nil a0)) = False) x0.
Definition term0 (a0 : Type') := forall y0 : a0, (@List.In a0 y0 (@nil a0)) = False.
