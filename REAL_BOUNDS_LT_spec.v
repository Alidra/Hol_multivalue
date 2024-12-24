Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1554983 : forall x : real, forall k : real, ((real_lt (real_neg k) x) /\ (real_lt x k)) = (real_lt (real_abs x) k).
