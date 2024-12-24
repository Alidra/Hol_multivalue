Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2519805 : forall m : int, forall n : int, (rem m (int_neg n)) = (rem m n).
