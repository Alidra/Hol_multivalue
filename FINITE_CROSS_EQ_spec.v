Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4330214 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@FINITE (prod A B) (@CROSS B A s t)) = ((s = (@EMPTY A)) \/ ((t = (@EMPTY B)) \/ ((@FINITE A s) /\ (@FINITE B t)))).
