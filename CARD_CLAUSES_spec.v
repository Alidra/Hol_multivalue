Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3840691 : forall {A : Type'}, ((@CARD A (@EMPTY A)) = (NUMERAL 0)) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> (@CARD A (@INSERT A x s)) = (@COND nat (@IN A x s) (@CARD A s) (S (@CARD A s)))).
