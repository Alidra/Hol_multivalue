Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1362595 : forall x : nat, forall n : nat, (real_pow (real_of_num x) n) = (real_of_num (Nat.pow x n)).
