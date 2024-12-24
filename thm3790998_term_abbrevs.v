Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a1, forall y1 : a0 -> Prop, forall y2 : nat, forall y3 : a1, forall y4 : type1411 a0 a1, (@FINREC a0 a1 y4 y0 y1 y3 (S y2)) = (exists y5 : a0, exists y6 : a1, (@IN a0 y5 y1) /\ ((@FINREC a0 a1 y4 y0 (@DELETE a0 y1 y5) y6 y2) /\ (y3 = (y4 y5 y6)))).
