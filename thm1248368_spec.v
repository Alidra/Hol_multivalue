Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248368 : forall (m : nat) (d : nat) (n : nat) (q : nat), (forall d' : nat, (((Nat.add m n) = (Nat.add (Nat.add (Nat.add m d) q) d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n q)))) /\ (((Nat.add (Nat.add m d) q) = (Nat.add (Nat.add m n) d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n q))))) = (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add (Nat.add m d) q))) (dist (@pair nat nat n q)))).
