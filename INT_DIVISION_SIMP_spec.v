Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2394130 : forall m : int, forall n : int, (int_add (int_mul (div m n) n) (rem m n)) = m.
