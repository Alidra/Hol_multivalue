Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2272662 : forall i : int, (int_neg i) = (int_of_real (real_neg (real_of_int i))).
