Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem22288 : forall a : Prop, forall b : Prop, forall c : Prop, (a \/ b) -> ((~ a) \/ c) -> b \/ c.
