Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1278399 : forall x : nadd, forall y : nadd, nadd_eq (nadd_mul x y) (nadd_mul y x).
