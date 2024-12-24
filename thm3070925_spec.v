Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3070925 : forall (x : int), (fun x' : int => (int_abs (int_abs x')) = (int_abs x')) x.
