Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247289 : forall (d : nat) (n : nat) (p : nat), (forall d' : nat, (((Nat.add p d) = (Nat.add n d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n p)))) /\ ((n = (Nat.add (Nat.add p d) d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n p))))) = (Peano.le d (Nat.add (dist (@pair nat nat (Nat.add p d) n)) (dist (@pair nat nat n p)))).
