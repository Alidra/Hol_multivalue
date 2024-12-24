Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1582667 : forall x : real, forall n : nat, (real_abs (real_pow x n)) = (real_pow (real_abs x) n).
