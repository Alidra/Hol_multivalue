Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3070799 : forall x : nat, forall y : nat, forall n : nat, (@eq2 nat x (Nat.modulo y n) (num_mod n)) = (@eq2 nat x y (num_mod n)).
