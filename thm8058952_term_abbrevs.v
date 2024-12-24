Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : a3) (x1 : a2) := (fun y0 : a2 => (@CASEWISE a0 a1 a2 a3 (@nil (prod (a1 -> a2) (a3 -> a1 -> a0))) x0 y0) = (@ε a0 (fun y1 : a0 => True))) x1.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') := forall y0 : a3, forall y1 : a2, (@CASEWISE a0 a1 a2 a3 (@nil (prod (a1 -> a2) (a3 -> a1 -> a0))) y0 y1) = (@ε a0 (fun y2 : a0 => True)).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : a3) := forall y0 : a2, (@CASEWISE a0 a1 a2 a3 (@nil (prod (a1 -> a2) (a3 -> a1 -> a0))) x0 y0) = (@ε a0 (fun y1 : a0 => True)).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (a3 : Type') (x0 : a3) := (fun y0 : a3 => forall y1 : a2, (@CASEWISE a0 a1 a2 a3 (@nil (prod (a1 -> a2) (a3 -> a1 -> a0))) y0 y1) = (@ε a0 (fun y2 : a0 => True))) x0.
