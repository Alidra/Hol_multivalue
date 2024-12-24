Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51 : forall (q : Prop) (p : Prop) (r : Prop), (p -> q) -> (q -> r) -> p -> r.
