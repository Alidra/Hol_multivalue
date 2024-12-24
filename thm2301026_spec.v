Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301026 : forall (n : int) (m : int), ((real_add (real_of_int m) (real_of_int n)) = (real_add (real_of_int n) (real_of_int m))) = ((int_add m n) = (int_add n m)).
