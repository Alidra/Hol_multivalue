Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7567170 : forall p : real -> real, forall q : real -> real, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : real => real_add (p x) (q x)).
