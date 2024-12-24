Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type16 a0 a1 a2) := forall y0 : cart a0 a1, forall y1 : cart a0 a2, x0 (@pastecart a0 a1 a2 y0 y1).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type16 a0 a1 a2) := forall y0 : type2 a0 a1 a2, x0 y0.
