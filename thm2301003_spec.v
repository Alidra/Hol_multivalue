Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301003 : forall (m : int) (n : int) (p : int), (int_add (int_add m n) p) = (int_add m (int_add n p)).
