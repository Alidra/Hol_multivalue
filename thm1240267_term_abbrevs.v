Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, x0 (x1 x2 x3 y0 y1 y2 y3 y4 y5)) x4.
Definition term16 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) (x7 : Prop) (x8 : Prop) (x9 : Prop) := x0 (x1 x2 x3 x4 x5 x6 x7 x8 x9).
Definition term3 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, x0 (x1 x2 y0 y1 y2 y3 y4 y5 y6)) x3.
Definition term11 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) (x7 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, x0 (x1 x2 x3 x4 x5 x6 y0 y1 y2)) x7.
Definition term1 (x0 : type1335) (x1 : type1539) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, x0 (x1 y0 y1 y2 y3 y4 y5 y6 y7)) x2.
Definition term9 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, x0 (x1 x2 x3 x4 x5 y0 y1 y2 y3)) x6.
Definition term13 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) (x7 : Prop) (x8 : Prop) := (fun y0 : Prop => forall y1 : Prop, x0 (x1 x2 x3 x4 x5 x6 x7 y0 y1)) x8.
Definition term12 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) (x7 : Prop) := forall y0 : Prop, forall y1 : Prop, x0 (x1 x2 x3 x4 x5 x6 x7 y0 y1).
Definition term10 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, x0 (x1 x2 x3 x4 x5 x6 y0 y1 y2).
Definition term8 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, x0 (x1 x2 x3 x4 x5 y0 y1 y2 y3).
Definition term6 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, x0 (x1 x2 x3 x4 y0 y1 y2 y3 y4).
Definition term4 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, x0 (x1 x2 x3 y0 y1 y2 y3 y4 y5).
Definition term2 (x0 : type1335) (x1 : type1539) (x2 : Prop) := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, x0 (x1 x2 y0 y1 y2 y3 y4 y5 y6).
Definition term0 (x0 : type1539) := fun y0 : type1678 => forall y1 : type1335, (forall y2 : type1678, (exists y3 : Prop, exists y4 : Prop, exists y5 : Prop, exists y6 : Prop, exists y7 : Prop, exists y8 : Prop, exists y9 : Prop, exists y10 : Prop, y2 = (x0 y3 y4 y5 y6 y7 y8 y9 y10)) -> y1 y2) -> y1 y0.
Definition term15 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) (x7 : Prop) (x8 : Prop) (x9 : Prop) := (fun y0 : Prop => x0 (x1 x2 x3 x4 x5 x6 x7 x8 y0)) x9.
Definition term14 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) (x6 : Prop) (x7 : Prop) (x8 : Prop) := forall y0 : Prop, x0 (x1 x2 x3 x4 x5 x6 x7 x8 y0).
Definition term7 (x0 : type1335) (x1 : type1539) (x2 : Prop) (x3 : Prop) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, x0 (x1 x2 x3 x4 y0 y1 y2 y3 y4)) x5.
