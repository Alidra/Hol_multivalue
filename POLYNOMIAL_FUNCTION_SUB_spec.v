Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7567846 : forall p : real -> real, forall q : real -> real, ((polynomial_function p) /\ (polynomial_function q)) -> polynomial_function (fun x : real => real_sub (p x) (q x)).
