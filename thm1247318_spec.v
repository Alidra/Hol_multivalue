Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247318 : forall (n : nat) (p : nat) (d : nat) (d' : nat) (h1 : n = (Nat.add (Nat.add p d) d')), (Peano.le d (Nat.add d' (dist (@pair nat nat (Nat.add (Nat.add p d) d') p)))) = (Peano.le d (Nat.add d' (dist (@pair nat nat n p)))).
