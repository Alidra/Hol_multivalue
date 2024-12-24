Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : prod a1 a0) (x2 : type1641 a0 a1) := @ASSOC a0 a1 x0 (@cons (prod a1 a0) x1 x2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : a1) (x2 : type1641 a0 a1) := @COND a0 ((@fst a1 a0 x0) = x1) (@snd a1 a0 x0) (@ASSOC a0 a1 x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : a1) (x2 : type1641 a0 a1) := (fun y0 : type1641 a0 a1 => (@ASSOC a0 a1 x1 (@cons (prod a1 a0) x0 y0)) = (@COND a0 ((@fst a1 a0 x0) = x1) (@snd a1 a0 x0) (@ASSOC a0 a1 x1 y0))) x2.
