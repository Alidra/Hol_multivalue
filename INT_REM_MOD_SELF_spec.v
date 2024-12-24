Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2528702 : forall m : int, forall n : int, @eq2 int (rem m n) m (int_mod n).
