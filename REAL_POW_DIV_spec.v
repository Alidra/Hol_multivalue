Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1595810 : forall x : real, forall y : real, forall n : nat, (real_pow (real_div x y) n) = (real_div (real_pow x n) (real_pow y n)).
