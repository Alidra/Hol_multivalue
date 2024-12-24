Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := forall y0 : type1219 a0 a1 a2 a3, (@GABS ((prod a1 (prod a3 a2)) -> a0) (fun y1 : type1219 a0 a1 a2 a3 => forall y2 : a1, forall y3 : a3, forall y4 : a2, @GEQ a0 (y1 (@pair a1 (prod a3 a2) y2 (@pair a3 a2 y3 y4))) (y0 (@pair a1 (prod a3 a2) y2 (@pair a3 a2 y3 y4))))) = y0.
