Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7594688 : forall {A : Type'}, forall s : A -> Prop, (@dimindex A s) = (@dimindex A (@UNIV A)).
