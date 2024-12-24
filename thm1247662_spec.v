Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247662 : forall (d : nat) (m : nat) (p : nat) (n : nat) (q : nat), (forall d' : nat, ((m = (Nat.add p d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n q)))) /\ ((p = (Nat.add m d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n q))))) = (Peano.le d (Nat.add (dist (@pair nat nat m p)) (dist (@pair nat nat n q)))).
