Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309952 : forall x : int, forall n : nat, (int_sgn (int_pow x n)) = (int_pow (int_sgn x) n).
