Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1470 a1 a2, forall y1 : type1517 a0 a1 a2, (@UNIONS a0 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a2, exists y4 : a1, @SETSPEC (a0 -> Prop) y2 (y0 y3 y4) (y1 y3 y4)))) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (exists y4 : a2, exists y5 : a1, (y0 y4 y5) /\ (@IN a0 y3 (y1 y4 y5))) y3)).
