Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem737 : forall (q : Prop) (p : Prop), (p \/ q) = (q \/ p).
