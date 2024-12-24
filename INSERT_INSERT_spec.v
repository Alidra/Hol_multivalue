Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3277193 : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@INSERT A x (@INSERT A x s)) = (@INSERT A x s).
