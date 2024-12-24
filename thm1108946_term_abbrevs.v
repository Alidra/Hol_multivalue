Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : list a0, forall y1 : list a1, (@ZIP a0 a1 (@cons a0 x0 y0) y1) = (@cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 y1)) (@ZIP a0 a1 y0 (@tl a1 y1))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) := forall y0 : list a1, (@ZIP a0 a1 (@cons a0 x0 x1) y0) = (@cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 y0)) (@ZIP a0 a1 x1 (@tl a1 y0))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, forall y2 : list a1, (@ZIP a0 a1 (@cons a0 y0 y1) y2) = (@cons (prod a0 a1) (@pair a0 a1 y0 (@hd a1 y2)) (@ZIP a0 a1 y1 (@tl a1 y2)))) x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) (x2 : list a1) := (fun y0 : list a1 => (@ZIP a0 a1 (@cons a0 x0 x1) y0) = (@cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 y0)) (@ZIP a0 a1 x1 (@tl a1 y0)))) x2.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => forall y1 : list a1, (@ZIP a0 a1 (@cons a0 x0 y0) y1) = (@cons (prod a0 a1) (@pair a0 a1 x0 (@hd a1 y1)) (@ZIP a0 a1 y0 (@tl a1 y1)))) x1.
