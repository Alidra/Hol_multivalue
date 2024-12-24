Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1275082 : forall x : nadd, forall y : nadd, nadd_le x (nadd_add x y).
