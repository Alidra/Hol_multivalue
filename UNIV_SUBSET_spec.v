Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3220332 : forall {A : Type'}, forall s : A -> Prop, (@SUBSET A (@UNIV A) s) = (s = (@UNIV A)).
