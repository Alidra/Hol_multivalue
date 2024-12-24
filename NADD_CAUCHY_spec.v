Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1262851 : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (Nat.mul m (dest_nadd x n)) (Nat.mul n (dest_nadd x m)))) (Nat.mul B (Nat.add m n)).
