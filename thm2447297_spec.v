Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2447297 : forall (b : int) (a : int), (fun a' : int => (int_divides a' b) = (exists x : int, b = (int_mul a' x))) a.
