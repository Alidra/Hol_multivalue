Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3220121 : forall {A : Type'}, forall s : A -> Prop, (@SUBSET A s (@EMPTY A)) = (s = (@EMPTY A)).
