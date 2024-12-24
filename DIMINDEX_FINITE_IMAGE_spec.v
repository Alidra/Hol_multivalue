Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7608063 : forall {A : Type'}, forall s : (finite_image A) -> Prop, forall t : A -> Prop, (@dimindex (finite_image A) s) = (@dimindex A t).
