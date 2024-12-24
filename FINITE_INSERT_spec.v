Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3608316 : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@FINITE A (@INSERT A x s)) = (@FINITE A s).
