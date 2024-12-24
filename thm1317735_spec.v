Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1317735 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.
