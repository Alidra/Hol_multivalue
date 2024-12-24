Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3281268 : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@UNION A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@UNION A s t) (@INSERT A x (@UNION A s t))).
