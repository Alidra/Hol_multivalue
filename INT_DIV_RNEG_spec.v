Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2519806 : forall m : int, forall n : int, (div m (int_neg n)) = (int_neg (div m n)).