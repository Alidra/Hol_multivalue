Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : type1541 => forall y1 : Ascii.ascii -> Prop, (forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, forall y9 : Prop, y1 (y0 y2 y3 y4 y5 y6 y7 y8 y9)) -> forall y2 : Ascii.ascii, y1 y2.
Definition term2 := (fun y0 : type1541 => forall y1 : Ascii.ascii -> Prop, (forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, forall y9 : Prop, y1 (y0 y2 y3 y4 y5 y6 y7 y8 y9)) -> forall y2 : Ascii.ascii, y1 y2) ASCII.
Definition term4 := @eq Prop ((fun y0 : type1541 => forall y1 : Ascii.ascii -> Prop, (forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, forall y9 : Prop, y1 (y0 y2 y3 y4 y5 y6 y7 y8 y9)) -> forall y2 : Ascii.ascii, y1 y2) _22730).
Definition term1 := (fun y0 : type1541 => forall y1 : Ascii.ascii -> Prop, (forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, forall y9 : Prop, y1 (y0 y2 y3 y4 y5 y6 y7 y8 y9)) -> forall y2 : Ascii.ascii, y1 y2) _22730.
Definition term5 := forall y0 : Ascii.ascii -> Prop, (forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, y0 (_22730 y1 y2 y3 y4 y5 y6 y7 y8)) -> forall y1 : Ascii.ascii, y0 y1.
Definition term3 := forall y0 : Ascii.ascii -> Prop, (forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, y0 (ASCII y1 y2 y3 y4 y5 y6 y7 y8)) -> forall y1 : Ascii.ascii, y0 y1.
Definition term6 := @eq Prop (forall y0 : Ascii.ascii -> Prop, (forall y1 : Prop, forall y2 : Prop, forall y3 : Prop, forall y4 : Prop, forall y5 : Prop, forall y6 : Prop, forall y7 : Prop, forall y8 : Prop, y0 (_22730 y1 y2 y3 y4 y5 y6 y7 y8)) -> forall y1 : Ascii.ascii, y0 y1).
