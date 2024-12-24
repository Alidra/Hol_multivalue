Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211464 : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall t : A -> Prop, (exists x : A, (@IN A x (@UNION A s t)) /\ (P x)) = ((exists x : A, (@IN A x s) /\ (P x)) \/ (exists x : A, (@IN A x t) /\ (P x))).
