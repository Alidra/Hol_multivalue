Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21107 : forall (p : Prop), (p -> ~ p) = (~ p).
