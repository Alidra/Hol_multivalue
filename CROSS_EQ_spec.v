Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4354438 : forall {A B : Type'}, forall s : A -> Prop, forall s' : A -> Prop, forall t : B -> Prop, forall t' : B -> Prop, ((@CROSS B A s t) = (@CROSS B A s' t')) = ((((s = (@EMPTY A)) \/ (t = (@EMPTY B))) /\ ((s' = (@EMPTY A)) \/ (t' = (@EMPTY B)))) \/ ((s = s') /\ (t = t'))).
