Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : int, forall y1 : int, (rem y0 (int_neg y1)) = (rem y0 y1).
