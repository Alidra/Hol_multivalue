Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type16 a0 a1 a2) := exists y0 : type2 a0 a1 a2, x0 y0.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type16 a0 a1 a2) := exists y0 : cart a0 a1, exists y1 : cart a0 a2, x0 (@pastecart a0 a1 a2 y0 y1).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type16 a0 a1 a2) := (~ ((exists y0 : type2 a0 a1 a2, x0 y0) = (exists y0 : cart a0 a1, exists y1 : cart a0 a2, x0 (@pastecart a0 a1 a2 y0 y1)))) -> False.
