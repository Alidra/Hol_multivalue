Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3216368 : forall {A : Type'}, forall s : A -> Prop, (exists x : A, @IN A x s) = (~ (s = (@EMPTY A))).
