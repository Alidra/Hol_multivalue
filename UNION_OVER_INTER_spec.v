Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3262316 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (@INTER A s (@UNION A t u)) = (@UNION A (@INTER A s t) (@INTER A s u)).
