Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7587039 : forall p : real -> real, forall q : real -> real, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (@o real real real p q).
