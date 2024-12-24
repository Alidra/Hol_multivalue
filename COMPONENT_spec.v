Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3272030 : forall {A : Type'}, forall x : A, forall s : A -> Prop, @IN A x (@INSERT A x s).
