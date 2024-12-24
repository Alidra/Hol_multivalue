Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305916 : forall (n : int) (m : int), ((real_mul (real_of_int m) (real_of_int n)) = (real_mul (real_of_int n) (real_of_int m))) = ((int_mul m n) = (int_mul n m)).
