Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2528714 : forall (m : int) (n : int) (p : int), @eq2 int (rem m (int_mul n p)) m (int_mod (int_mul n p)).
