Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1980265 : forall (y : real) (x : real), (fun x' : real => (real_gt x' y) = (real_lt y x')) x.