Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7223171 : forall p : nat, forall f : nat -> real, forall m : nat, forall n : nat, (@sum nat (dotdot (Nat.add m p) (Nat.add n p)) f) = (@sum nat (dotdot m n) (fun i : nat => f (Nat.add i p))).
