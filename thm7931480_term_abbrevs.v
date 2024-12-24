Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := (fun y0 : finite_sum a0 a0 => ((@mktybit0 a0 x0) = (@mktybit0 a0 y0)) = (x0 = y0)) x1.
