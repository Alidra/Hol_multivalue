Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := forall y0 : type1644 a0 a1 a2 a3, forall y1 : type1633 a0 a1 a2 a3, forall y2 : a3, forall y3 : a2, (@CASEWISE a0 a1 a2 a3 (@cons (prod (a1 -> a2) (a3 -> a1 -> a0)) y0 y1) y2 y3) = (@COND a0 (exists y4 : a1, (@fst (a1 -> a2) (a3 -> a1 -> a0) y0 y4) = y3) (@snd (a1 -> a2) (a3 -> a1 -> a0) y0 y2 (@ε a1 (fun y4 : a1 => (@fst (a1 -> a2) (a3 -> a1 -> a0) y0 y4) = y3))) (@CASEWISE a0 a1 a2 a3 y1 y2 y3)).
