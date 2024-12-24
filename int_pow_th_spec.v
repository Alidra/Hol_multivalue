Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2294268 : forall x : int, forall n : nat, (real_of_int (int_pow x n)) = (real_pow (real_of_int x) n).
