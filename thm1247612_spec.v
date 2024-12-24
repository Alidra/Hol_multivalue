Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247612 : forall (m : nat) (p : nat) (n : nat) (q : nat), (forall d : nat, (((Nat.add m n) = (Nat.add (Nat.add p q) d)) -> Peano.le d (Nat.add (dist (@pair nat nat m p)) (dist (@pair nat nat n q)))) /\ (((Nat.add p q) = (Nat.add (Nat.add m n) d)) -> Peano.le d (Nat.add (dist (@pair nat nat m p)) (dist (@pair nat nat n q))))) = (Peano.le (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (Nat.add (dist (@pair nat nat m p)) (dist (@pair nat nat n q)))).
