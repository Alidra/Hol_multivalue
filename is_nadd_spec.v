Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1262615 : forall x : nat -> nat, (is_nadd x) = (exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (Nat.mul m (x n)) (Nat.mul n (x m)))) (Nat.mul B (Nat.add m n))).
