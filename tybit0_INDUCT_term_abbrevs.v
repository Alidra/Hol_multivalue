Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := fun y0 : type46 a0 => forall y1 : type1345 a0, (forall y2 : finite_sum a0 a0, y1 (y0 y2)) -> forall y2 : tybit0 a0, y1 y2.
Definition term4 (a0 : Type') := @eq Prop ((fun y0 : type46 a0 => forall y1 : type1345 a0, (forall y2 : finite_sum a0 a0, y1 (y0 y2)) -> forall y2 : tybit0 a0, y1 y2) (@_103783 a0)).
Definition term2 (a0 : Type') := (fun y0 : type46 a0 => forall y1 : type1345 a0, (forall y2 : finite_sum a0 a0, y1 (y0 y2)) -> forall y2 : tybit0 a0, y1 y2) (@mktybit0 a0).
Definition term1 (a0 : Type') := (fun y0 : type46 a0 => forall y1 : type1345 a0, (forall y2 : finite_sum a0 a0, y1 (y0 y2)) -> forall y2 : tybit0 a0, y1 y2) (@_103783 a0).
Definition term5 (a0 : Type') := forall y0 : type1345 a0, (forall y1 : finite_sum a0 a0, y0 (@_103783 a0 y1)) -> forall y1 : tybit0 a0, y0 y1.
Definition term3 (a0 : Type') := forall y0 : type1345 a0, (forall y1 : finite_sum a0 a0, y0 (@mktybit0 a0 y1)) -> forall y1 : tybit0 a0, y0 y1.
Definition term6 (a0 : Type') := @eq Prop (forall y0 : type1345 a0, (forall y1 : finite_sum a0 a0, y0 (@_103783 a0 y1)) -> forall y1 : tybit0 a0, y0 y1).
