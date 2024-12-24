Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) := (fun y0 : a1 => forall y1 : a1, (@FINREC a0 a1 x0 y1 x1 y0 (NUMERAL 0)) = ((x1 = (@EMPTY a0)) /\ (y0 = y1))) x2.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type1411 a0 a1, forall y1 : a0 -> Prop, forall y2 : a1, forall y3 : a1, (@FINREC a0 a1 y0 y3 y1 y2 (NUMERAL 0)) = ((y1 = (@EMPTY a0)) /\ (y2 = y3)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1, forall y2 : a1, (@FINREC a0 a1 x0 y2 y0 y1 (NUMERAL 0)) = ((y0 = (@EMPTY a0)) /\ (y1 = y2))) x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := (fun y0 : type1411 a0 a1 => forall y1 : a0 -> Prop, forall y2 : a1, forall y3 : a1, (@FINREC a0 a1 y0 y3 y1 y2 (NUMERAL 0)) = ((y1 = (@EMPTY a0)) /\ (y2 = y3))) x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) (x3 : a1) := (fun y0 : a1 => (@FINREC a0 a1 x0 y0 x1 x2 (NUMERAL 0)) = ((x1 = (@EMPTY a0)) /\ (x2 = y0))) x3.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) := forall y0 : a1, forall y1 : a1, (@FINREC a0 a1 x0 y1 x1 y0 (NUMERAL 0)) = ((x1 = (@EMPTY a0)) /\ (y0 = y1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) := forall y0 : a0 -> Prop, forall y1 : a1, forall y2 : a1, (@FINREC a0 a1 x0 y2 y0 y1 (NUMERAL 0)) = ((y0 = (@EMPTY a0)) /\ (y1 = y2)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1411 a0 a1) (x1 : a0 -> Prop) (x2 : a1) := forall y0 : a1, (@FINREC a0 a1 x0 y0 x1 x2 (NUMERAL 0)) = ((x1 = (@EMPTY a0)) /\ (x2 = y0)).
