Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3287457 : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@SUBSET A (@INSERT A x s) t) = ((@IN A x t) /\ (@SUBSET A s t)).
