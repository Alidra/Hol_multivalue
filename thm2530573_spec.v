Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2530573 : forall (p : int) (m : int) (n : int), @eq2 int (rem m (int_mul n p)) m (int_mod n).
