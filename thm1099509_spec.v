Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1099509 : forall {_25272 : Type'}, forall n : nat, forall x : _25272, (@repeat_with_perm_args _25272 (S n) x) = (@cons _25272 x (@repeat_with_perm_args _25272 n x)).
