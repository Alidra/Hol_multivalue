Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem12653 : forall {A : Type'} (t1 : A) (t2 : A), ((@COND A True t1 t2) = t1) /\ ((@COND A False t1 t2) = t2).
