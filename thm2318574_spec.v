Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318574 : forall (x : int) (y : int), (fun y' : int => (x = y') = ((real_of_int x) = (real_of_int y'))) y.
