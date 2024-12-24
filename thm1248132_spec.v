Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248132 : forall (n : nat) (q : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)), (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add (Nat.add p d) n) (Nat.add p q))) (dist (@pair nat nat n q)))) = (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (dist (@pair nat nat n q)))).
