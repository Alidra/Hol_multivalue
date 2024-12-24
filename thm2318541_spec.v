Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318541 : forall (x : int), (fun x' : int => (real_of_int (int_neg x')) = (real_neg (real_of_int x'))) x.
