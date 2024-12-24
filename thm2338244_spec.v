Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338244 : forall (t2 : Prop) (t1 : Prop), ((fun t2' : Prop => ((~ t1) -> ~ t2') = (t2' -> t1)) t2) = (((~ t1) -> ~ t2) = (t2 -> t1)).
