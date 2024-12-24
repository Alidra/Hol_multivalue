Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : ind, forall y1 : ind, ((IND_SUC y0) = (IND_SUC y1)) = (y0 = y1).
