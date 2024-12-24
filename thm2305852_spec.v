Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305852 : forall (n : int) (m : int) (p : int), (int_mul m (int_mul n p)) = (int_mul n (int_mul m p)).
