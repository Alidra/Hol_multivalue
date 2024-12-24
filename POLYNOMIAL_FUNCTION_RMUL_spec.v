Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7567593 : forall p : real -> real, forall c : real, (polynomial_function p) -> polynomial_function (fun x : real => real_mul (p x) c).
