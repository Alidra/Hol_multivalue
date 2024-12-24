Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301359 : forall x : int, forall k : int, ((int_le (int_neg k) x) /\ (int_le x k)) = (int_le (int_abs x) k).
