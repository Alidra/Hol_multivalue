Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305813 : forall (n : real) (m : real) (p : real), ((real_mul (real_mul m n) p) = (real_mul m (real_mul n p))) /\ ((real_mul m (real_mul n p)) = (real_mul n (real_mul m p))).
