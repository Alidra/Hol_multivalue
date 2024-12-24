Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3074596 : forall (b : nat) (a : nat), (exists x : int, (int_of_num b) = (int_mul (int_of_num a) x)) = (exists x : nat, b = (Nat.mul a x)).
