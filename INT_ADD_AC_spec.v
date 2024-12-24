Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301028 : forall (n : int) (m : int) (p : int), ((int_add m n) = (int_add n m)) /\ (((int_add (int_add m n) p) = (int_add m (int_add n p))) /\ ((int_add m (int_add n p)) = (int_add n (int_add m p)))).
