Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : Prop => fun y1 : Prop => fun y2 : Prop => fun y3 : Prop => fun y4 : Prop => fun y5 : Prop => fun y6 : Prop => fun y7 : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) (NUMERAL 0) (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) y0 (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) y1 (@pair Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) y2 (@pair Prop (prod Prop (prod Prop (prod Prop Prop))) y3 (@pair Prop (prod Prop (prod Prop Prop)) y4 (@pair Prop (prod Prop Prop) y5 (@pair Prop Prop y6 y7))))))) (fun y8 : nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))).
