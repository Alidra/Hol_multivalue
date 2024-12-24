Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2530574 : forall (n : int) (m : int) (p : int), (rem (rem m (int_mul n p)) p) = (rem m p).
