Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1267473 : forall x : nadd, forall y : nadd, exists A : nat, exists B : nat, forall n : nat, Peano.le (dist (@pair nat nat (Nat.mul n (dest_nadd x (dest_nadd y n))) (Nat.mul (dest_nadd x n) (dest_nadd y n)))) (Nat.add (Nat.mul A n) B).
