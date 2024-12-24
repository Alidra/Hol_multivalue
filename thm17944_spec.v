Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem17944 : forall (t1 : Prop) (t2 : Prop) (t3 : Prop), ((fun t3' : Prop => (t1 /\ (t2 /\ t3')) = ((t1 /\ t2) /\ t3')) t3) = ((t1 /\ (t2 /\ t3)) = ((t1 /\ t2) /\ t3)).
