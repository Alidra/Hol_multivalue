Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2437518 : forall x : int, forall y : int, forall n : int, (@eq2 int x y (int_mod n)) = (exists d : int, (int_sub x y) = (int_mul n d)).