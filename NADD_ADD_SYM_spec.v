Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1274476 : forall x : nadd, forall y : nadd, nadd_eq (nadd_add x y) (nadd_add y x).
