Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982797 : forall (x : real) (y : real), ((fun y' : real => (real_div x y') = (real_mul x (real_inv y'))) y) = ((real_div x y) = (real_mul x (real_inv y))).
