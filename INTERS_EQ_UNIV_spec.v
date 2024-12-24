Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3363571 : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@INTERS A f) = (@UNIV A)) = (forall s : A -> Prop, (@IN (A -> Prop) s f) -> s = (@UNIV A)).
