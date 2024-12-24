Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3458986 : forall (t1 : Prop) (t2 : Prop) (t3 : Prop), ((t1 \/ t2) \/ t3) = (t1 \/ (t2 \/ t3)).
