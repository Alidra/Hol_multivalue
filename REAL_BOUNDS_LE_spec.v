Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1553652 : forall x : real, forall k : real, ((real_le (real_neg k) x) /\ (real_le x k)) = (real_le (real_abs x) k).
