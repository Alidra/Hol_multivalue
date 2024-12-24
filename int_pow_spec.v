Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2294056 : forall x : int, forall n : nat, (int_pow x n) = (int_of_real (real_pow (real_of_int x) n)).
