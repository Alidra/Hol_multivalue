Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem15721 : forall (a : unit), (one_ABS (one_REP a)) = a.
