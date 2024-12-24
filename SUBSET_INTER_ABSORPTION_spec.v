Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3258170 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@SUBSET A s t) = ((@INTER A s t) = s).
