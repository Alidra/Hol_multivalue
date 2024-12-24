Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3284766 : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@INTER A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@INSERT A x (@INTER A s t)) (@INTER A s t)).
