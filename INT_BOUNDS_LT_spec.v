Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301398 : forall x : int, forall k : int, ((int_lt (int_neg k) x) /\ (int_lt x k)) = (int_lt (int_abs x) k).
