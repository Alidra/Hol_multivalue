Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3216589 : forall {A : Type'} (s : A -> Prop), (forall x : A, @IN A x s) = (s = (@UNIV A)).
