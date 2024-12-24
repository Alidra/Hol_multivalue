Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3864294 : forall {A : Type'}, forall s : A -> Prop, (@HAS_SIZE A s (NUMERAL 0)) = (s = (@EMPTY A)).
