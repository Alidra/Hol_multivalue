Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1467 a0 a1) (x2 : list a1) (x3 : a0) := (fun y0 : a0 => (@ITLIST a0 a1 x1 (@cons a1 x0 x2) y0) = (x1 x0 (@ITLIST a0 a1 x1 x2 y0))) x3.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1467 a0 a1) (x2 : list a1) (x3 : a0) := x1 x0 (@ITLIST a0 a1 x1 x2 x3).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1467 a0 a1) (x1 : a1) (x2 : list a1) (x3 : a0) := @ITLIST a0 a1 x0 (@cons a1 x1 x2) x3.
