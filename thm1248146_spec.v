Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248146 : forall (n : nat) (q : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)), (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add (Nat.add m d) q))) (dist (@pair nat nat n q)))) = (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (dist (@pair nat nat n q)))).
