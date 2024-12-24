Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1475 a0 a1 a2) (x2 : list a1) (x3 : list a2) := @cons a0 (x1 x0 (@hd a2 x3)) (@MAP2 a0 a1 a2 x1 x2 (@tl a2 x3)).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1475 a0 a1 a2) (x1 : a1) (x2 : list a1) (x3 : list a2) := @MAP2 a0 a1 a2 x0 (@cons a1 x1 x2) x3.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1) (x1 : type1475 a0 a1 a2) (x2 : list a1) (x3 : list a2) := (fun y0 : list a2 => (@MAP2 a0 a1 a2 x1 (@cons a1 x0 x2) y0) = (@cons a0 (x1 x0 (@hd a2 y0)) (@MAP2 a0 a1 a2 x1 x2 (@tl a2 y0)))) x3.
