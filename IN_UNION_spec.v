Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3204949 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@IN A x (@UNION A s t)) = ((@IN A x s) \/ (@IN A x t)).
