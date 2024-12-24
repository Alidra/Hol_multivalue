Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307775 : forall x : int, forall m : nat, forall n : nat, (int_pow x (Nat.add m n)) = (int_mul (int_pow x m) (int_pow x n)).
