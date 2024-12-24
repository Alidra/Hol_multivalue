Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem71260 : forall (a : nat), (mk_num (dest_num a)) = a.
