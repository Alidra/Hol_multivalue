Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303844 : forall x : int, forall y : int, forall z : int, (int_lt y (int_add x (int_neg z))) = (int_lt (int_add y z) x).
