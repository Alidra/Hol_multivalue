Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1248166 : forall (d : nat) (p : nat) (n : nat) (q : nat), (forall d' : nat, (((Nat.add (Nat.add p d) n) = (Nat.add (Nat.add p q) d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n q)))) /\ (((Nat.add p q) = (Nat.add (Nat.add (Nat.add p d) n) d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n q))))) = (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add (Nat.add p d) n) (Nat.add p q))) (dist (@pair nat nat n q)))).
