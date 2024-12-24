Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247255 : forall (n : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)), (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add p d) n)) (dist (@pair nat nat n p)))) = (Peano.le d (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n p)))).
