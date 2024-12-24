Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307411 : forall x : nat, forall n : nat, (int_pow (int_of_num x) n) = (int_of_num (Nat.pow x n)).
