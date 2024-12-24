Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : type1644 a0 a1 a2 a3) (x1 : type1633 a0 a1 a2 a3) (x2 : a3) (x3 : a2) := @COND a0 (exists y0 : a1, (@fst (a1 -> a2) (a3 -> a1 -> a0) x0 y0) = x3) (@snd (a1 -> a2) (a3 -> a1 -> a0) x0 x2 (@ε a1 (fun y0 : a1 => (@fst (a1 -> a2) (a3 -> a1 -> a0) x0 y0) = x3))) (@CASEWISE a0 a1 a2 a3 x1 x2 x3).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : type1644 a0 a1 a2 a3) (x1 : type1633 a0 a1 a2 a3) (x2 : a3) (x3 : a2) := @CASEWISE a0 a1 a2 a3 (@cons (prod (a1 -> a2) (a3 -> a1 -> a0)) x0 x1) x2 x3.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : type1644 a0 a1 a2 a3) (x1 : type1633 a0 a1 a2 a3) (x2 : a3) (x3 : a2) := ((@CASEWISE a0 a1 a2 a3 (@nil (prod (a1 -> a2) (a3 -> a1 -> a0))) x2 x3) = (@ε a0 (fun y0 : a0 => True))) /\ ((@CASEWISE a0 a1 a2 a3 (@cons (prod (a1 -> a2) (a3 -> a1 -> a0)) x0 x1) x2 x3) = (@COND a0 (exists y0 : a1, (@fst (a1 -> a2) (a3 -> a1 -> a0) x0 y0) = x3) (@snd (a1 -> a2) (a3 -> a1 -> a0) x0 x2 (@ε a1 (fun y0 : a1 => (@fst (a1 -> a2) (a3 -> a1 -> a0) x0 y0) = x3))) (@CASEWISE a0 a1 a2 a3 x1 x2 x3))).
