Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2400155 : forall m : int, forall n : int, (rem m n) = (int_sub m (int_mul (div m n) n)).
