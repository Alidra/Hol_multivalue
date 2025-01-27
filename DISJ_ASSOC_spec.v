Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem693 : forall t1 : Prop, forall t2 : Prop, forall t3 : Prop, (t1 \/ (t2 \/ t3)) = ((t1 \/ t2) \/ t3).
