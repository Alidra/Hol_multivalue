Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := @ε ind (fun y0 : ind => (forall y1 : ind, forall y2 : ind, ((IND_SUC y1) = (IND_SUC y2)) = (y1 = y2)) /\ (forall y1 : ind, ~ ((IND_SUC y1) = y0))).
