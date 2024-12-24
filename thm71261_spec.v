Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem71261 : forall (r : ind), (NUM_REP r) = ((dest_num (mk_num r)) = r).
