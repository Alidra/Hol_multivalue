Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2528201 : forall x : int, forall y : int, forall n : int, (@eq2 int (rem x n) y (int_mod n)) = (@eq2 int x y (int_mod n)).
