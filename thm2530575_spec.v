Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2530575 : forall (p : int) (m : int) (n : int), (rem (rem m (int_mul n p)) n) = (rem m n).
