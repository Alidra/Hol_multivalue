Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term0 (a0 : Type') (x0 : type1143 a0) := (fun y0 : type1143 a0 => ((y0 (@nil a0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 y2) -> y0 (@cons a0 y1 y2))) -> forall y1 : list a0, y0 y1) x0.