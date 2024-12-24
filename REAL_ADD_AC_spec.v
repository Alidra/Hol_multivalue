Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1352530 : forall (n : real) (m : real) (p : real), ((real_add m n) = (real_add n m)) /\ (((real_add (real_add m n) p) = (real_add m (real_add n p))) /\ ((real_add m (real_add n p)) = (real_add n (real_add m p)))).
