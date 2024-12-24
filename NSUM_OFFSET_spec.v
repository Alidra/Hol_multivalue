Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7048726 : forall p : nat, forall f : nat -> nat, forall m : nat, forall n : nat, (@nsum nat (dotdot (Nat.add m p) (Nat.add n p)) f) = (@nsum nat (dotdot m n) (fun i : nat => f (Nat.add i p))).
