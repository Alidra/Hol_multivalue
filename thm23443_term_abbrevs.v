Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term5 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => x0 = y0).
Definition term8 (a0 : Type') (x0 : a0) := @eq a0 (@ε a0 (fun y0 : a0 => y0 = x0)).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term10 (a0 : Type') := forall y0 : a0, (@ε a0 (fun y1 : a0 => y0 = y1)) = y0.
Definition term7 (a0 : Type') (x0 : a0) := @eq a0 (@ε a0 (fun y0 : a0 => x0 = y0)).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term4 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term6 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => y0 = x0).
Definition term3 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term9 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@ε a0 (fun y1 : a0 => y1 = y0)) = y0) x0.