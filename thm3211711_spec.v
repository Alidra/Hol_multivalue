Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211711 : forall {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop), ((fun x' : A => (@IN A x' (@INTER A s t)) = ((@IN A x' s) /\ (@IN A x' t))) x) = ((@IN A x (@INTER A s t)) = ((@IN A x s) /\ (@IN A x t))).
