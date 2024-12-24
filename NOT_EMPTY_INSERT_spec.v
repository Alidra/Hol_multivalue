Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3279167 : forall {A : Type'}, forall x : A, forall s : A -> Prop, ~ ((@EMPTY A) = (@INSERT A x s)).
