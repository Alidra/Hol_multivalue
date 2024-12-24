Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem22025 : forall a : Prop, forall c : Prop, a -> ((~ a) \/ c) -> c.
