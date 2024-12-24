Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3237011 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@UNION A s t) = (@EMPTY A)) = ((s = (@EMPTY A)) /\ (t = (@EMPTY A))).
