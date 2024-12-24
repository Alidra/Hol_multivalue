Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3236047 : forall {A : Type'}, (forall s : A -> Prop, (@UNION A (@UNIV A) s) = (@UNIV A)) /\ (forall s : A -> Prop, (@UNION A s (@UNIV A)) = (@UNIV A)).
