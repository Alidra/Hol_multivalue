Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem310011 : forall (t1 : Prop) (t2 : Prop), ((fun t2' : Prop => (~ (t1 -> t2')) = (t1 /\ (~ t2'))) t2) = ((~ (t1 -> t2)) = (t1 /\ (~ t2))).
