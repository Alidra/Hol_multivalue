Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3263548 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@UNION A s (@INTER A t u)) = (@INTER A (@UNION A s t) (@UNION A s u)).
