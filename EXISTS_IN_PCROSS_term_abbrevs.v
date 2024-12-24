Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) (x1 : type24 a0 a2) (x2 : type16 a0 a1 a2) := exists y0 : type2 a0 a1 a2, (@IN (cart a0 (finite_sum a1 a2)) y0 (@PCROSS a0 a1 a2 x0 x1)) /\ (x2 y0).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type24 a0 a1) (x1 : type24 a0 a2) (x2 : type16 a0 a1 a2) := exists y0 : cart a0 a1, exists y1 : cart a0 a2, (@IN (cart a0 a1) y0 x0) /\ ((@IN (cart a0 a2) y1 x1) /\ (x2 (@pastecart a0 a1 a2 y0 y1))).
