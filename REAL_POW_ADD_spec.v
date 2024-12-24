Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1596102 : forall x : real, forall m : nat, forall n : nat, (real_pow x (Nat.add m n)) = (real_mul (real_pow x m) (real_pow x n)).
