Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211739 : forall {A : Type'} (s : A -> Prop) (t : A -> Prop), ((fun t' : A -> Prop => (@DISJOINT A s t') = ((@INTER A s t') = (@EMPTY A))) t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
