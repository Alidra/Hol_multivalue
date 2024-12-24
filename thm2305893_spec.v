Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305893 : forall (m : int) (n : int) (p : int), (int_mul (int_mul m n) p) = (int_mul m (int_mul n p)).
