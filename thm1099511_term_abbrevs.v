Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : a0, (@repeat_with_perm_args a0 (NUMERAL 0) y0) = (@nil a0).
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@repeat_with_perm_args a0 (NUMERAL 0) y0) = (@nil a0)) x0.
