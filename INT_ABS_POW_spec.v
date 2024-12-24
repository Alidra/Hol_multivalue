Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300556 : forall x : int, forall n : nat, (int_abs (int_pow x n)) = (int_pow (int_abs x) n).
