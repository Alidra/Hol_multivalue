Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @UNION a0 x0 (@UNIONS a0 x1).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @UNIONS a0 (@INSERT (a0 -> Prop) x0 x1).
