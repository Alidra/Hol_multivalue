Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247241 : forall (m : nat) (n : nat) (p : nat), (forall d : nat, ((m = (Nat.add p d)) -> Peano.le d (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n p)))) /\ ((p = (Nat.add m d)) -> Peano.le d (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n p))))) = (Peano.le (dist (@pair nat nat m p)) (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n p)))).
