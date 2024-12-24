Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1317782 : forall (m : nat), (hreal_of_num m) = (mk_hreal (nadd_eq (nadd_of_num m))).
