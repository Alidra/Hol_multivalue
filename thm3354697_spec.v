Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3354697 : forall {A : Type'}, forall x : A, (@IN A x (@INTERS A (@EMPTY (A -> Prop)))) = (@IN A x (@UNIV A)).
