Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1758099 : forall x : real, forall n : nat, (real_sgn (real_pow x n)) = (real_pow (real_sgn x) n).
