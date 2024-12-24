Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (a4 : Type') (a5 : Type') (a6 : Type') (a7 : Type') (a8 : Type') := (forall y0 : type1219 a0 a1 a2 a3, (@GABS ((prod a1 (prod a3 a2)) -> a0) (fun y1 : type1219 a0 a1 a2 a3 => forall y2 : a1, forall y3 : a3, forall y4 : a2, @GEQ a0 (y1 (@pair a1 (prod a3 a2) y2 (@pair a3 a2 y3 y4))) (y0 (@pair a1 (prod a3 a2) y2 (@pair a3 a2 y3 y4))))) = y0) /\ (forall y0 : type1218 a4 a5 a6 a7 a8, (@GABS ((prod a5 (prod a6 (prod a8 a7))) -> a4) (fun y1 : type1218 a4 a5 a6 a7 a8 => forall y2 : a5, forall y3 : a6, forall y4 : a8, forall y5 : a7, @GEQ a4 (y1 (@pair a5 (prod a6 (prod a8 a7)) y2 (@pair a6 (prod a8 a7) y3 (@pair a8 a7 y4 y5)))) (y0 (@pair a5 (prod a6 (prod a8 a7)) y2 (@pair a6 (prod a8 a7) y3 (@pair a8 a7 y4 y5)))))) = y0).
