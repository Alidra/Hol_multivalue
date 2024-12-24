Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1264303 : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (dest_nadd x (Nat.mul m n)) (Nat.mul m (dest_nadd x n)))) (Nat.add (Nat.mul B m) B).
