Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1980260 : forall (y : real) (x : real), ((fun x' : real => (real_ge x' y) = (real_le y x')) x) = ((real_ge x y) = (real_le y x)).
