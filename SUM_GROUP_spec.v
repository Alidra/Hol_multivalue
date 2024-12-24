Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7160834 : forall {A B : Type'}, forall f : A -> B, forall g : A -> real, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (@SUBSET B (@IMAGE A B f s) t)) -> (@sum B t (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_325 : A => exists x : A, @SETSPEC A GEN_PVAR_325 ((@IN A x s) /\ ((f x) = y)) x)) g)) = (@sum A s g).
