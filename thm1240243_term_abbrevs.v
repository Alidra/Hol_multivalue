Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : type1539) := fun y0 : type1678 => forall y1 : type1335, (forall y2 : type1678, (exists y3 : Prop, exists y4 : Prop, exists y5 : Prop, exists y6 : Prop, exists y7 : Prop, exists y8 : Prop, exists y9 : Prop, exists y10 : Prop, y2 = (x0 y3 y4 y5 y6 y7 y8 y9 y10)) -> y1 y2) -> y1 y0.
Definition term1 (x0 : type1539) (x1 : type1335) := forall y0 : type1335, (forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, y0 (x0 y1 y2 y3 y4 y5 y6 y7 y8)) -> forall y1 : type1678, (x1 y1) -> y0 y1.
