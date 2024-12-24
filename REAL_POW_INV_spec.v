Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1595679 : forall x : real, forall n : nat, (real_pow (real_inv x) n) = (real_inv (real_pow x n)).
