Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248118 : forall (m : nat) (p : nat) (n : nat) (q : nat), (forall d : nat, ((m = (Nat.add p d)) -> Peano.le d (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (dist (@pair nat nat n q)))) /\ ((p = (Nat.add m d)) -> Peano.le d (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (dist (@pair nat nat n q))))) = (Peano.le (dist (@pair nat nat m p)) (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (dist (@pair nat nat n q)))).
