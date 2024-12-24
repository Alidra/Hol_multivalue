Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2406287 : forall (x : int) (y : int), (fun y' : int => (int_sub x y') = (int_add x (int_neg y'))) y.
